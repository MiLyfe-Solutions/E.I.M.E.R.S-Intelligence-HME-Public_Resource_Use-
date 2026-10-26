import V185TrunkScan23Chunk0217

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1289158 : List Nat := [6, 1, 3, 1, 1, 1, 2, 1, 2, 5]
def baseStart_1289158 : Nat := 118140960795 + 1289158 * 2 ^ 59
def prefixEnd_1289158 : Nat := 4983230072969 + 3 ^ 40 * 1289158 * 2
def baseEnd_1289158 : Nat := 220652564529657465698759

theorem tailTrace_1289158 : CollatzResearch.WordTrace tailWord_1289158 prefixEnd_1289158 220652564529657465698759 := by
  unfold tailWord_1289158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1469357970737756609463379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31346303375738807668552085 1469357970737756609463379)
  ·
    refine ⟨2204036956106634914195069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1469357970737756609463379 2204036956106634914195069)
    ·
      refine ⟨826513858539988092823151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2204036956106634914195069 826513858539988092823151)
      ·
        refine ⟨1239770787809982139234727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 826513858539988092823151 1239770787809982139234727)
        ·
          refine ⟨1859656181714973208852091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1239770787809982139234727 1859656181714973208852091)
          ·
            refine ⟨2789484272572459813278137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1859656181714973208852091 2789484272572459813278137)
            ·
              refine ⟨2092113204429344859958603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2789484272572459813278137 2092113204429344859958603)
              ·
                refine ⟨3138169806644017289937905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2092113204429344859958603 3138169806644017289937905)
                ·
                  refine ⟨2353627354983012967453429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3138169806644017289937905 2353627354983012967453429)
                  ·
                    refine ⟨220652564529657465698759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2353627354983012967453429 220652564529657465698759)
                    ·
                      rfl

theorem cell23_1289158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_1289158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289158 prefixEnd_1289158 := by exact prefixLift 1289158
  have htrace : WordTrace (prefixWord ++ tailWord_1289158) baseStart_1289158 baseEnd_1289158 := by
    simpa [prefixWord, tailWord_1289158, baseEnd_1289158] using wordTrace_append hprefix tailTrace_1289158
  have hstable : (prefixWord ++ tailWord_1289158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289158).length < 2 ^ (prefixWord ++ tailWord_1289158).sum := by decide
  have hdescent : baseEnd_1289158 < baseStart_1289158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289187 : List Nat := [1, 1, 1, 6, 1, 1, 1, 4, 2, 3, 2]
def baseStart_1289187 : Nat := 118140960795 + 1289187 * 2 ^ 59
def prefixEnd_1289187 : Nat := 4983230072969 + 3 ^ 40 * 1289187 * 2
def baseEnd_1289187 : Nat := 661972584527952783633643

theorem tailTrace_1289187 : CollatzResearch.WordTrace tailWord_1289187 prefixEnd_1289187 661972584527952783633643 := by
  unfold tailWord_1289187
  simp only [CollatzResearch.WordTrace]
  refine ⟨47020512780503149455633815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31347008520335432970422543 47020512780503149455633815)
  ·
    refine ⟨70530769170754724183450723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47020512780503149455633815 70530769170754724183450723)
    ·
      refine ⟨105796153756132086275176085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70530769170754724183450723 105796153756132086275176085)
      ·
        refine ⟨4959194707318691544148879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 105796153756132086275176085 4959194707318691544148879)
        ·
          refine ⟨7438792060978037316223319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4959194707318691544148879 7438792060978037316223319)
          ·
            refine ⟨11158188091467055974334979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7438792060978037316223319 11158188091467055974334979)
            ·
              refine ⟨16737282137200583961502469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11158188091467055974334979 16737282137200583961502469)
              ·
                refine ⟨3138240400725109492781713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16737282137200583961502469 3138240400725109492781713)
                ·
                  refine ⟨2353680300543832119586285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3138240400725109492781713 2353680300543832119586285)
                  ·
                    refine ⟨882630112703937044844857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2353680300543832119586285 882630112703937044844857)
                    ·
                      refine ⟨661972584527952783633643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 882630112703937044844857 661972584527952783633643)
                      ·
                        rfl

theorem cell23_1289187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_1289187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289187 prefixEnd_1289187 := by exact prefixLift 1289187
  have htrace : WordTrace (prefixWord ++ tailWord_1289187) baseStart_1289187 baseEnd_1289187 := by
    simpa [prefixWord, tailWord_1289187, baseEnd_1289187] using wordTrace_append hprefix tailTrace_1289187
  have hstable : (prefixWord ++ tailWord_1289187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289187).length < 2 ^ (prefixWord ++ tailWord_1289187).sum := by decide
  have hdescent : baseEnd_1289187 < baseStart_1289187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289200 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 2, 6, 2]
def baseStart_1289200 : Nat := 118140960795 + 1289200 * 2 ^ 59
def prefixEnd_1289200 : Nat := 4983230072969 + 3 ^ 40 * 1289200 * 2
def baseEnd_1289200 : Nat := 661979259776461232771083

theorem tailTrace_1289200 : CollatzResearch.WordTrace tailWord_1289200 prefixEnd_1289200 661979259776461232771083 := by
  unfold tailWord_1289200
  simp only [CollatzResearch.WordTrace]
  refine ⟨23510493464728026337928527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31347324619637368450571369 23510493464728026337928527)
  ·
    refine ⟨35265740197092039506892791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23510493464728026337928527 35265740197092039506892791)
    ·
      refine ⟨52898610295638059260339187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35265740197092039506892791 52898610295638059260339187)
      ·
        refine ⟨79347915443457088890508781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52898610295638059260339187 79347915443457088890508781)
        ·
          refine ⟨29755468291296408333940793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79347915443457088890508781 29755468291296408333940793)
          ·
            refine ⟨22316601218472306250455595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29755468291296408333940793 22316601218472306250455595)
            ·
              refine ⟨33474901827708459375683393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22316601218472306250455595 33474901827708459375683393)
              ·
                refine ⟨25106176370781344531762545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33474901827708459375683393 25106176370781344531762545)
                ·
                  refine ⟨18829632278086008398821909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25106176370781344531762545 18829632278086008398821909)
                  ·
                    refine ⟨882639013035281643694777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18829632278086008398821909 882639013035281643694777)
                    ·
                      refine ⟨661979259776461232771083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 882639013035281643694777 661979259776461232771083)
                      ·
                        rfl

theorem cell23_1289200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 6, 2].length) (baseStart_1289200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289200 prefixEnd_1289200 := by exact prefixLift 1289200
  have htrace : WordTrace (prefixWord ++ tailWord_1289200) baseStart_1289200 baseEnd_1289200 := by
    simpa [prefixWord, tailWord_1289200, baseEnd_1289200] using wordTrace_append hprefix tailTrace_1289200
  have hstable : (prefixWord ++ tailWord_1289200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289200).length < 2 ^ (prefixWord ++ tailWord_1289200).sum := by decide
  have hdescent : baseEnd_1289200 < baseStart_1289200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289251 : List Nat := [1, 1, 1, 4, 3, 2, 2, 4, 1, 2, 2]
def baseStart_1289251 : Nat := 118140960795 + 1289251 * 2 ^ 59
def prefixEnd_1289251 : Nat := 4983230072969 + 3 ^ 40 * 1289251 * 2
def baseEnd_1289251 : Nat := 662005447289840533233349

theorem tailTrace_1289251 : CollatzResearch.WordTrace tailWord_1289251 prefixEnd_1289251 662005447289840533233349 := by
  unfold tailWord_1289251
  simp only [CollatzResearch.WordTrace]
  refine ⟨47022847052271288385963607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31348564701514192257309071 47022847052271288385963607)
  ·
    refine ⟨70534270578406932578945411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47022847052271288385963607 70534270578406932578945411)
    ·
      refine ⟨105801405867610398868418117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70534270578406932578945411 105801405867610398868418117)
      ·
        refine ⟨19837763600176949787828397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105801405867610398868418117 19837763600176949787828397)
        ·
          refine ⟨7439161350066356170435649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19837763600176949787828397 7439161350066356170435649)
          ·
            refine ⟨5579371012549767127826737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7439161350066356170435649 5579371012549767127826737)
            ·
              refine ⟨4184528259412325345870053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5579371012549767127826737 4184528259412325345870053)
              ·
                refine ⟨784599048639811002350635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4184528259412325345870053 784599048639811002350635)
                ·
                  refine ⟨1176898572959716503525953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 784599048639811002350635 1176898572959716503525953)
                  ·
                    refine ⟨882673929719787377644465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1176898572959716503525953 882673929719787377644465)
                    ·
                      refine ⟨662005447289840533233349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 882673929719787377644465 662005447289840533233349)
                      ·
                        rfl

theorem cell23_1289251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4, 1, 2, 2].length) (baseStart_1289251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289251 prefixEnd_1289251 := by exact prefixLift 1289251
  have htrace : WordTrace (prefixWord ++ tailWord_1289251) baseStart_1289251 baseEnd_1289251 := by
    simpa [prefixWord, tailWord_1289251, baseEnd_1289251] using wordTrace_append hprefix tailTrace_1289251
  have hstable : (prefixWord ++ tailWord_1289251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289251).length < 2 ^ (prefixWord ++ tailWord_1289251).sum := by decide
  have hdescent : baseEnd_1289251 < baseStart_1289251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289294 : List Nat := [4, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2]
def baseStart_1289294 : Nat := 118140960795 + 1289294 * 2 ^ 59
def prefixEnd_1289294 : Nat := 4983230072969 + 3 ^ 40 * 1289294 * 2
def baseEnd_1289294 : Nat := 662027526957983864995651

theorem tailTrace_1289294 : CollatzResearch.WordTrace tailWord_1289294 prefixEnd_1289294 662027526957983864995651 := by
  unfold tailWord_1289294
  simp only [CollatzResearch.WordTrace]
  refine ⟨5878051923889438341222367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31349610260743671153185957 5878051923889438341222367)
  ·
    refine ⟨8817077885834157511833551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5878051923889438341222367 8817077885834157511833551)
    ·
      refine ⟨13225616828751236267750327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8817077885834157511833551 13225616828751236267750327)
      ·
        refine ⟨19838425243126854401625491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13225616828751236267750327 19838425243126854401625491)
        ·
          refine ⟨29757637864690281602438237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19838425243126854401625491 29757637864690281602438237)
          ·
            refine ⟨11159114199258855600914339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29757637864690281602438237 11159114199258855600914339)
            ·
              refine ⟨16738671298888283401371509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11159114199258855600914339 16738671298888283401371509)
              ·
                refine ⟨1569250434270776568878579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16738671298888283401371509 1569250434270776568878579)
                ·
                  refine ⟨2353875651406164853317869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1569250434270776568878579 2353875651406164853317869)
                  ·
                    refine ⟨882703369277311819994201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2353875651406164853317869 882703369277311819994201)
                    ·
                      refine ⟨662027526957983864995651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 882703369277311819994201 662027526957983864995651)
                      ·
                        rfl

theorem cell23_1289294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2].length) (baseStart_1289294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289294 prefixEnd_1289294 := by exact prefixLift 1289294
  have htrace : WordTrace (prefixWord ++ tailWord_1289294) baseStart_1289294 baseEnd_1289294 := by
    simpa [prefixWord, tailWord_1289294, baseEnd_1289294] using wordTrace_append hprefix tailTrace_1289294
  have hstable : (prefixWord ++ tailWord_1289294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289294).length < 2 ^ (prefixWord ++ tailWord_1289294).sum := by decide
  have hdescent : baseEnd_1289294 < baseStart_1289294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289300 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 4, 6]
def baseStart_1289300 : Nat := 118140960795 + 1289300 * 2 ^ 59
def prefixEnd_1289300 : Nat := 4983230072969 + 3 ^ 40 * 1289300 * 2
def baseEnd_1289300 : Nat := 220676869280636947173541

theorem tailTrace_1289300 : CollatzResearch.WordTrace tailWord_1289300 prefixEnd_1289300 220676869280636947173541 := by
  unfold tailWord_1289300
  simp only [CollatzResearch.WordTrace]
  refine ⟨23512317114546884877248677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31349756152729179836331569 23512317114546884877248677)
  ·
    refine ⟨4408559458977540914484127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23512317114546884877248677 4408559458977540914484127)
    ·
      refine ⟨6612839188466311371726191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4408559458977540914484127 6612839188466311371726191)
      ·
        refine ⟨9919258782699467057589287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6612839188466311371726191 9919258782699467057589287)
        ·
          refine ⟨14878888174049200586383931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9919258782699467057589287 14878888174049200586383931)
          ·
            refine ⟨22318332261073800879575897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14878888174049200586383931 22318332261073800879575897)
            ·
              refine ⟨16738749195805350659681923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22318332261073800879575897 16738749195805350659681923)
              ·
                refine ⟨25108123793708025989522885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16738749195805350659681923 25108123793708025989522885)
                ·
                  refine ⟨4707773211320254873035541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25108123793708025989522885 4707773211320254873035541)
                  ·
                    refine ⟨220676869280636947173541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4707773211320254873035541 220676869280636947173541)
                    ·
                      rfl

theorem cell23_1289300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_1289300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289300 prefixEnd_1289300 := by exact prefixLift 1289300
  have htrace : WordTrace (prefixWord ++ tailWord_1289300) baseStart_1289300 baseEnd_1289300 := by
    simpa [prefixWord, tailWord_1289300, baseEnd_1289300] using wordTrace_append hprefix tailTrace_1289300
  have hstable : (prefixWord ++ tailWord_1289300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289300).length < 2 ^ (prefixWord ++ tailWord_1289300).sum := by decide
  have hdescent : baseEnd_1289300 < baseStart_1289300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289302 : List Nat := [5, 2, 2, 1, 3, 1, 1, 1, 3, 2, 2]
def baseStart_1289302 : Nat := 118140960795 + 1289302 * 2 ^ 59
def prefixEnd_1289302 : Nat := 4983230072969 + 3 ^ 40 * 1289302 * 2
def baseEnd_1289302 : Nat := 662031634803219833695615

theorem tailTrace_1289302 : CollatzResearch.WordTrace tailWord_1289302 prefixEnd_1289302 662031634803219833695615 := by
  unfold tailWord_1289302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2939044198442907756004385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31349804783391016064046773 2939044198442907756004385)
  ·
    refine ⟨2204283148832180817003289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2939044198442907756004385 2204283148832180817003289)
    ·
      refine ⟨1653212361624135612752467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2204283148832180817003289 1653212361624135612752467)
      ·
        refine ⟨2479818542436203419128701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1653212361624135612752467 2479818542436203419128701)
        ·
          refine ⟨929931953413576282173263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2479818542436203419128701 929931953413576282173263)
          ·
            refine ⟨1394897930120364423259895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 929931953413576282173263 1394897930120364423259895)
            ·
              refine ⟨2092346895180546634889843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1394897930120364423259895 2092346895180546634889843)
              ·
                refine ⟨3138520342770819952334765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2092346895180546634889843 3138520342770819952334765)
                ·
                  refine ⟨1176945128539057482125537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3138520342770819952334765 1176945128539057482125537)
                  ·
                    refine ⟨882708846404293111594153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1176945128539057482125537 882708846404293111594153)
                    ·
                      refine ⟨662031634803219833695615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 882708846404293111594153 662031634803219833695615)
                      ·
                        rfl

theorem cell23_1289302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_1289302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289302 prefixEnd_1289302 := by exact prefixLift 1289302
  have htrace : WordTrace (prefixWord ++ tailWord_1289302) baseStart_1289302 baseEnd_1289302 := by
    simpa [prefixWord, tailWord_1289302, baseEnd_1289302] using wordTrace_append hprefix tailTrace_1289302
  have hstable : (prefixWord ++ tailWord_1289302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289302).length < 2 ^ (prefixWord ++ tailWord_1289302).sum := by decide
  have hdescent : baseEnd_1289302 < baseStart_1289302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289330 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 9]
def baseStart_1289330 : Nat := 118140960795 + 1289330 * 2 ^ 59
def prefixEnd_1289330 : Nat := 4983230072969 + 3 ^ 40 * 1289330 * 2
def baseEnd_1289330 : Nat := 73560668029060636016165

theorem tailTrace_1289330 : CollatzResearch.WordTrace tailWord_1289330 prefixEnd_1289330 73560668029060636016165 := by
  unfold tailWord_1289330
  simp only [CollatzResearch.WordTrace]
  refine ⟨11756432104746271219522361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31350485612656723252059629 11756432104746271219522361)
  ·
    refine ⟨8817324078559703414641771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11756432104746271219522361 8817324078559703414641771)
    ·
      refine ⟨13225986117839555121962657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8817324078559703414641771 13225986117839555121962657)
      ·
        refine ⟨9919489588379666341471993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13225986117839555121962657 9919489588379666341471993)
        ·
          refine ⟨7439617191284749756103995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9919489588379666341471993 7439617191284749756103995)
          ·
            refine ⟨11159425786927124634155993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7439617191284749756103995 11159425786927124634155993)
            ·
              refine ⟨8369569340195343475616995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11159425786927124634155993 8369569340195343475616995)
              ·
                refine ⟨12554354010293015213425493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8369569340195343475616995 12554354010293015213425493)
                ·
                  refine ⟨73560668029060636016165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12554354010293015213425493 73560668029060636016165)
                  ·
                    rfl

theorem cell23_1289330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 9].length) (baseStart_1289330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289330 prefixEnd_1289330 := by exact prefixLift 1289330
  have htrace : WordTrace (prefixWord ++ tailWord_1289330) baseStart_1289330 baseEnd_1289330 := by
    simpa [prefixWord, tailWord_1289330, baseEnd_1289330] using wordTrace_append hprefix tailTrace_1289330
  have hstable : (prefixWord ++ tailWord_1289330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289330).length < 2 ^ (prefixWord ++ tailWord_1289330).sum := by decide
  have hdescent : baseEnd_1289330 < baseStart_1289330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289347 : List Nat := [1, 1, 1, 3, 3, 2, 2, 5, 5]
def baseStart_1289347 : Nat := 118140960795 + 1289347 * 2 ^ 59
def prefixEnd_1289347 : Nat := 4983230072969 + 3 ^ 40 * 1289347 * 2
def baseEnd_1289347 : Nat := 73561637936963573070323

theorem tailTrace_1289347 : CollatzResearch.WordTrace tailWord_1289347 prefixEnd_1289347 73561637936963573070323 := by
  unfold tailWord_1289347
  simp only [CollatzResearch.WordTrace]
  refine ⟨47026348459923496781458295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31350898973282331187638863 47026348459923496781458295)
  ·
    refine ⟨70539522689885245172187443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47026348459923496781458295 70539522689885245172187443)
    ·
      refine ⟨105809284034827867758281165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70539522689885245172187443 105809284034827867758281165)
      ·
        refine ⟨39678481513060450409355437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105809284034827867758281165 39678481513060450409355437)
        ·
          refine ⟨14879430567397668903508289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39678481513060450409355437 14879430567397668903508289)
          ·
            refine ⟨11159572925548251677631217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14879430567397668903508289 11159572925548251677631217)
            ·
              refine ⟨8369679694161188758223413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11159572925548251677631217 8369679694161188758223413)
              ·
                refine ⟨784657471327611446083445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8369679694161188758223413 784657471327611446083445)
                ·
                  refine ⟨73561637936963573070323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 784657471327611446083445 73561637936963573070323)
                  ·
                    rfl

theorem cell23_1289347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5, 5].length) (baseStart_1289347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289347 prefixEnd_1289347 := by exact prefixLift 1289347
  have htrace : WordTrace (prefixWord ++ tailWord_1289347) baseStart_1289347 baseEnd_1289347 := by
    simpa [prefixWord, tailWord_1289347, baseEnd_1289347] using wordTrace_append hprefix tailTrace_1289347
  have hstable : (prefixWord ++ tailWord_1289347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289347).length < 2 ^ (prefixWord ++ tailWord_1289347).sum := by decide
  have hdescent : baseEnd_1289347 < baseStart_1289347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289358 : List Nat := [4, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2]
def baseStart_1289358 : Nat := 118140960795 + 1289358 * 2 ^ 59
def prefixEnd_1289358 : Nat := 4983230072969 + 3 ^ 40 * 1289358 * 2
def baseEnd_1289358 : Nat := 662060389719871614595357

theorem tailTrace_1289358 : CollatzResearch.WordTrace tailWord_1289358 prefixEnd_1289358 662060389719871614595357 := by
  unfold tailWord_1289358
  simp only [CollatzResearch.WordTrace]
  refine ⟨5878343707860455707513591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31351166441922430440072485 5878343707860455707513591)
  ·
    refine ⟨8817515561790683561270387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5878343707860455707513591 8817515561790683561270387)
    ·
      refine ⟨13226273342686025341905581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8817515561790683561270387 13226273342686025341905581)
      ·
        refine ⟨4959852503507259503214593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13226273342686025341905581 4959852503507259503214593)
        ·
          refine ⟨3719889377630444627410945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4959852503507259503214593 3719889377630444627410945)
          ·
            refine ⟨2789917033222833470558209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3719889377630444627410945 2789917033222833470558209)
            ·
              refine ⟨2092437774917125102918657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2789917033222833470558209 2092437774917125102918657)
              ·
                refine ⟨1569328331187843827188993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2092437774917125102918657 1569328331187843827188993)
                ·
                  refine ⟨1176996248390882870391745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1569328331187843827188993 1176996248390882870391745)
                  ·
                    refine ⟨882747186293162152793809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1176996248390882870391745 882747186293162152793809)
                    ·
                      refine ⟨662060389719871614595357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 882747186293162152793809 662060389719871614595357)
                      ·
                        rfl

theorem cell23_1289358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_1289358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289358 prefixEnd_1289358 := by exact prefixLift 1289358
  have htrace : WordTrace (prefixWord ++ tailWord_1289358) baseStart_1289358 baseEnd_1289358 := by
    simpa [prefixWord, tailWord_1289358, baseEnd_1289358] using wordTrace_append hprefix tailTrace_1289358
  have hstable : (prefixWord ++ tailWord_1289358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289358).length < 2 ^ (prefixWord ++ tailWord_1289358).sum := by decide
  have hdescent : baseEnd_1289358 < baseStart_1289358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289360 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 4, 5]
def baseStart_1289360 : Nat := 118140960795 + 1289360 * 2 ^ 59
def prefixEnd_1289360 : Nat := 4983230072969 + 3 ^ 40 * 1289360 * 2
def baseEnd_1289360 : Nat := 220687138893726868923449

theorem tailTrace_1289360 : CollatzResearch.WordTrace tailWord_1289360 prefixEnd_1289360 220687138893726868923449 := by
  unfold tailWord_1289360
  simp only [CollatzResearch.WordTrace]
  refine ⟨23513411304438200000840767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31351215072584266667787689 23513411304438200000840767)
  ·
    refine ⟨35270116956657300001261151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23513411304438200000840767 35270116956657300001261151)
    ·
      refine ⟨52905175434985950001891727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35270116956657300001261151 52905175434985950001891727)
      ·
        refine ⟨79357763152478925002837591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52905175434985950001891727 79357763152478925002837591)
        ·
          refine ⟨119036644728718387504256387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79357763152478925002837591 119036644728718387504256387)
          ·
            refine ⟨178554967093077581256384581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119036644728718387504256387 178554967093077581256384581)
            ·
              refine ⟨33479056329952046485572109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 178554967093077581256384581 33479056329952046485572109)
              ·
                refine ⟨12554646123732017432089541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33479056329952046485572109 12554646123732017432089541)
                ·
                  refine ⟨2353996148199753268516789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12554646123732017432089541 2353996148199753268516789)
                  ·
                    refine ⟨220687138893726868923449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2353996148199753268516789 220687138893726868923449)
                    ·
                      rfl

theorem cell23_1289360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 4, 5].length) (baseStart_1289360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289360 prefixEnd_1289360 := by exact prefixLift 1289360
  have htrace : WordTrace (prefixWord ++ tailWord_1289360) baseStart_1289360 baseEnd_1289360 := by
    simpa [prefixWord, tailWord_1289360, baseEnd_1289360] using wordTrace_append hprefix tailTrace_1289360
  have hstable : (prefixWord ++ tailWord_1289360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289360).length < 2 ^ (prefixWord ++ tailWord_1289360).sum := by decide
  have hdescent : baseEnd_1289360 < baseStart_1289360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289374 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_1289374 : Nat := 118140960795 + 1289374 * 2 ^ 59
def prefixEnd_1289374 : Nat := 4983230072969 + 3 ^ 40 * 1289374 * 2
def baseEnd_1289374 : Nat := 662068605410343551995283

theorem tailTrace_1289374 : CollatzResearch.WordTrace tailWord_1289374 prefixEnd_1289374 662068605410343551995283 := by
  unfold tailWord_1289374
  simp only [CollatzResearch.WordTrace]
  refine ⟨5878416653853210049086397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31351555487217120261794117 5878416653853210049086397)
  ·
    refine ⟨2204406245194953768407399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5878416653853210049086397 2204406245194953768407399)
    ·
      refine ⟨3306609367792430652611099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2204406245194953768407399 3306609367792430652611099)
      ·
        refine ⟨4959914051688645978916649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3306609367792430652611099 4959914051688645978916649)
        ·
          refine ⟨3719935538766484484187487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4959914051688645978916649 3719935538766484484187487)
          ·
            refine ⟨5579903308149726726281231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3719935538766484484187487 5579903308149726726281231)
            ·
              refine ⟨8369854962224590089421847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5579903308149726726281231 8369854962224590089421847)
              ·
                refine ⟨12554782443336885134132771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8369854962224590089421847 12554782443336885134132771)
                ·
                  refine ⟨18832173665005327701199157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12554782443336885134132771 18832173665005327701199157)
                  ·
                    refine ⟨1765516281094249471987421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18832173665005327701199157 1765516281094249471987421)
                    ·
                      refine ⟨662068605410343551995283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1765516281094249471987421 662068605410343551995283)
                      ·
                        rfl

theorem cell23_1289374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_1289374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289374 prefixEnd_1289374 := by exact prefixLift 1289374
  have htrace : WordTrace (prefixWord ++ tailWord_1289374) baseStart_1289374 baseEnd_1289374 := by
    simpa [prefixWord, tailWord_1289374, baseEnd_1289374] using wordTrace_append hprefix tailTrace_1289374
  have hstable : (prefixWord ++ tailWord_1289374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289374).length < 2 ^ (prefixWord ++ tailWord_1289374).sum := by decide
  have hdescent : baseEnd_1289374 < baseStart_1289374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289394 : List Nat := [3, 2, 1, 1, 1, 6, 1, 1, 2, 5]
def baseStart_1289394 : Nat := 118140960795 + 1289394 * 2 ^ 59
def prefixEnd_1289394 : Nat := 4983230072969 + 3 ^ 40 * 1289394 * 2
def baseEnd_1289394 : Nat := 220692958341144491248397

theorem tailTrace_1289394 : CollatzResearch.WordTrace tailWord_1289394 prefixEnd_1289394 220692958341144491248397 := by
  unfold tailWord_1289394
  simp only [CollatzResearch.WordTrace]
  refine ⟨11757015672688305952104809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31352041793835482538946157 11757015672688305952104809)
  ·
    refine ⟨8817761754516229464078607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11757015672688305952104809 8817761754516229464078607)
    ·
      refine ⟨13226642631774344196117911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8817761754516229464078607 13226642631774344196117911)
      ·
        refine ⟨19839963947661516294176867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13226642631774344196117911 19839963947661516294176867)
        ·
          refine ⟨29759945921492274441265301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19839963947661516294176867 29759945921492274441265301)
          ·
            refine ⟨1394997465069950364434311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 29759945921492274441265301 1394997465069950364434311)
            ·
              refine ⟨2092496197604925546651467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1394997465069950364434311 2092496197604925546651467)
              ·
                refine ⟨3138744296407388319977201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2092496197604925546651467 3138744296407388319977201)
                ·
                  refine ⟨2354058222305541239982901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3138744296407388319977201 2354058222305541239982901)
                  ·
                    refine ⟨220692958341144491248397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2354058222305541239982901 220692958341144491248397)
                    ·
                      rfl

theorem cell23_1289394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_1289394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289394 prefixEnd_1289394 := by exact prefixLift 1289394
  have htrace : WordTrace (prefixWord ++ tailWord_1289394) baseStart_1289394 baseEnd_1289394 := by
    simpa [prefixWord, tailWord_1289394, baseEnd_1289394] using wordTrace_append hprefix tailTrace_1289394
  have hstable : (prefixWord ++ tailWord_1289394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289394).length < 2 ^ (prefixWord ++ tailWord_1289394).sum := by decide
  have hdescent : baseEnd_1289394 < baseStart_1289394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289400 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 2, 3, 5]
def baseStart_1289400 : Nat := 118140960795 + 1289400 * 2 ^ 59
def prefixEnd_1289400 : Nat := 4983230072969 + 3 ^ 40 * 1289400 * 2
def baseEnd_1289400 : Nat := 662081955907360450270163

theorem tailTrace_1289400 : CollatzResearch.WordTrace tailWord_1289400 prefixEnd_1289400 662081955907360450270163 := by
  unfold tailWord_1289400
  simp only [CollatzResearch.WordTrace]
  refine ⟨23514140764365743416568827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31352187685820991222091769 23514140764365743416568827)
  ·
    refine ⟨35271211146548615124853241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23514140764365743416568827 35271211146548615124853241)
    ·
      refine ⟨26453408359911461343639931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35271211146548615124853241 26453408359911461343639931)
      ·
        refine ⟨39680112539867192015459897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26453408359911461343639931 39680112539867192015459897)
        ·
          refine ⟨29760084404900394011594923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39680112539867192015459897 29760084404900394011594923)
          ·
            refine ⟨44640126607350591017392385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29760084404900394011594923 44640126607350591017392385)
            ·
              refine ⟨33480094955512943263044289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44640126607350591017392385 33480094955512943263044289)
              ·
                refine ⟨25110071216634707447283217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33480094955512943263044289 25110071216634707447283217)
                ·
                  refine ⟨18832553412476030585462413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25110071216634707447283217 18832553412476030585462413)
                  ·
                    refine ⟨7062207529678511469548405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18832553412476030585462413 7062207529678511469548405)
                    ·
                      refine ⟨662081955907360450270163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7062207529678511469548405 662081955907360450270163)
                      ·
                        rfl

theorem cell23_1289400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_1289400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289400 prefixEnd_1289400 := by exact prefixLift 1289400
  have htrace : WordTrace (prefixWord ++ tailWord_1289400) baseStart_1289400 baseEnd_1289400 := by
    simpa [prefixWord, tailWord_1289400, baseEnd_1289400] using wordTrace_append hprefix tailTrace_1289400
  have hstable : (prefixWord ++ tailWord_1289400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289400).length < 2 ^ (prefixWord ++ tailWord_1289400).sum := by decide
  have hdescent : baseEnd_1289400 < baseStart_1289400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289501 : List Nat := [1, 4, 2, 3, 1, 1, 3, 2, 1, 5]
def baseStart_1289501 : Nat := 118140960795 + 1289501 * 2 ^ 59
def prefixEnd_1289501 : Nat := 4983230072969 + 3 ^ 40 * 1289501 * 2
def baseEnd_1289501 : Nat := 220711272484488185035733

theorem tailTrace_1289501 : CollatzResearch.WordTrace tailWord_1289501 prefixEnd_1289501 220711272484488185035733 := by
  unfold tailWord_1289501
  simp only [CollatzResearch.WordTrace]
  refine ⟨47031965301365581082564357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31354643534243720721709571 47031965301365581082564357)
  ·
    refine ⟨8818493494006046452980817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47031965301365581082564357 8818493494006046452980817)
    ·
      refine ⟨6613870120504534839735613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8818493494006046452980817 6613870120504534839735613)
      ·
        refine ⟨2480201295189200564900855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6613870120504534839735613 2480201295189200564900855)
        ·
          refine ⟨3720301942783800847351283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2480201295189200564900855 3720301942783800847351283)
          ·
            refine ⟨5580452914175701271026925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3720301942783800847351283 5580452914175701271026925)
            ·
              refine ⟨2092669842815887976635097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5580452914175701271026925 2092669842815887976635097)
              ·
                refine ⟨1569502382111915982476323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2092669842815887976635097 1569502382111915982476323)
                ·
                  refine ⟨2354253573167873973714485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1569502382111915982476323 2354253573167873973714485)
                  ·
                    refine ⟨220711272484488185035733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2354253573167873973714485 220711272484488185035733)
                    ·
                      rfl

theorem cell23_1289501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_1289501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289501 prefixEnd_1289501 := by exact prefixLift 1289501
  have htrace : WordTrace (prefixWord ++ tailWord_1289501) baseStart_1289501 baseEnd_1289501 := by
    simpa [prefixWord, tailWord_1289501, baseEnd_1289501] using wordTrace_append hprefix tailTrace_1289501
  have hstable : (prefixWord ++ tailWord_1289501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289501).length < 2 ^ (prefixWord ++ tailWord_1289501).sum := by decide
  have hdescent : baseEnd_1289501 < baseStart_1289501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289514 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 3, 6]
def baseStart_1289514 : Nat := 118140960795 + 1289514 * 2 ^ 59
def prefixEnd_1289514 : Nat := 4983230072969 + 3 ^ 40 * 1289514 * 2
def baseEnd_1289514 : Nat := 220713497567324334748213

theorem tailTrace_1289514 : CollatzResearch.WordTrace tailWord_1289514 prefixEnd_1289514 220713497567324334748213 := by
  unfold tailWord_1289514
  simp only [CollatzResearch.WordTrace]
  refine ⟨11758109862579621075696899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31354959633545656201858397 11758109862579621075696899)
  ·
    refine ⟨17637164793869431613545349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11758109862579621075696899 17637164793869431613545349)
    ·
      refine ⟨3306968398850518427539753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17637164793869431613545349 3306968398850518427539753)
      ·
        refine ⟨2480226299137888820654815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3306968398850518427539753 2480226299137888820654815)
        ·
          refine ⟨3720339448706833230982223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2480226299137888820654815 3720339448706833230982223)
          ·
            refine ⟨5580509173060249846473335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3720339448706833230982223 5580509173060249846473335)
            ·
              refine ⟨8370763759590374769710003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5580509173060249846473335 8370763759590374769710003)
              ·
                refine ⟨12556145639385562154565005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8370763759590374769710003 12556145639385562154565005)
                ·
                  refine ⟨4708554614769585807961877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12556145639385562154565005 4708554614769585807961877)
                  ·
                    refine ⟨220713497567324334748213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4708554614769585807961877 220713497567324334748213)
                    ·
                      rfl

theorem cell23_1289514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_1289514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289514 prefixEnd_1289514 := by exact prefixLift 1289514
  have htrace : WordTrace (prefixWord ++ tailWord_1289514) baseStart_1289514 baseEnd_1289514 := by
    simpa [prefixWord, tailWord_1289514, baseEnd_1289514] using wordTrace_append hprefix tailTrace_1289514
  have hstable : (prefixWord ++ tailWord_1289514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289514).length < 2 ^ (prefixWord ++ tailWord_1289514).sum := by decide
  have hdescent : baseEnd_1289514 < baseStart_1289514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289534 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_1289534 : Nat := 118140960795 + 1289534 * 2 ^ 59
def prefixEnd_1289534 : Nat := 4983230072969 + 3 ^ 40 * 1289534 * 2
def baseEnd_1289534 : Nat := 662150762315062925994547

theorem tailTrace_1289534 : CollatzResearch.WordTrace tailWord_1289534 prefixEnd_1289534 662150762315062925994547 := by
  unfold tailWord_1289534
  simp only [CollatzResearch.WordTrace]
  refine ⟨5879146113780753464814457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31355445940164018479010437 5879146113780753464814457)
  ·
    refine ⟨4409359585335565098610843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5879146113780753464814457 4409359585335565098610843)
    ·
      refine ⟨6614039378003347647916265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4409359585335565098610843 6614039378003347647916265)
      ·
        refine ⟨4960529533502510735937199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6614039378003347647916265 4960529533502510735937199)
        ·
          refine ⟨7440794300253766103905799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4960529533502510735937199 7440794300253766103905799)
          ·
            refine ⟨11161191450380649155858699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7440794300253766103905799 11161191450380649155858699)
            ·
              refine ⟨16741787175570973733788049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11161191450380649155858699 16741787175570973733788049)
              ·
                refine ⟨12556340381678230300341037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16741787175570973733788049 12556340381678230300341037)
                ·
                  refine ⟨4708627643129336362627889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12556340381678230300341037 4708627643129336362627889)
                  ·
                    refine ⟨3531470732347002271970917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4708627643129336362627889 3531470732347002271970917)
                    ·
                      refine ⟨662150762315062925994547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3531470732347002271970917 662150762315062925994547)
                      ·
                        rfl

theorem cell23_1289534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_1289534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289534 prefixEnd_1289534 := by exact prefixLift 1289534
  have htrace : WordTrace (prefixWord ++ tailWord_1289534) baseStart_1289534 baseEnd_1289534 := by
    simpa [prefixWord, tailWord_1289534, baseEnd_1289534] using wordTrace_append hprefix tailTrace_1289534
  have hstable : (prefixWord ++ tailWord_1289534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289534).length < 2 ^ (prefixWord ++ tailWord_1289534).sum := by decide
  have hdescent : baseEnd_1289534 < baseStart_1289534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289567 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 5]
def baseStart_1289567 : Nat := 118140960795 + 1289567 * 2 ^ 59
def prefixEnd_1289567 : Nat := 4983230072969 + 3 ^ 40 * 1289567 * 2
def baseEnd_1289567 : Nat := 662167707176661296881895

theorem tailTrace_1289567 : CollatzResearch.WordTrace tailWord_1289567 prefixEnd_1289567 662167707176661296881895 := by
  unfold tailWord_1289567
  simp only [CollatzResearch.WordTrace]
  refine ⟨47034372519126474354466955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31356248346084316236311303 47034372519126474354466955)
  ·
    refine ⟨70551558778689711531700433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47034372519126474354466955 70551558778689711531700433)
    ·
      refine ⟨52913669084017283648775325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70551558778689711531700433 52913669084017283648775325)
      ·
        refine ⟨19842625906506481368290747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52913669084017283648775325 19842625906506481368290747)
        ·
          refine ⟨29763938859759722052436121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19842625906506481368290747 29763938859759722052436121)
          ·
            refine ⟨22322954144819791539327091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29763938859759722052436121 22322954144819791539327091)
            ·
              refine ⟨33484431217229687308990637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22322954144819791539327091 33484431217229687308990637)
              ·
                refine ⟨12556661706461132740871489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33484431217229687308990637 12556661706461132740871489)
                ·
                  refine ⟨9417496279845849555653617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12556661706461132740871489 9417496279845849555653617)
                  ·
                    refine ⟨7063122209884387166740213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9417496279845849555653617 7063122209884387166740213)
                    ·
                      refine ⟨662167707176661296881895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7063122209884387166740213 662167707176661296881895)
                      ·
                        rfl

theorem cell23_1289567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_1289567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289567 prefixEnd_1289567 := by exact prefixLift 1289567
  have htrace : WordTrace (prefixWord ++ tailWord_1289567) baseStart_1289567 baseEnd_1289567 := by
    simpa [prefixWord, tailWord_1289567, baseEnd_1289567] using wordTrace_append hprefix tailTrace_1289567
  have hstable : (prefixWord ++ tailWord_1289567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289567).length < 2 ^ (prefixWord ++ tailWord_1289567).sum := by decide
  have hdescent : baseEnd_1289567 < baseStart_1289567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289575 : List Nat := [1, 1, 5, 1, 4, 2, 2, 1, 1, 2, 3]
def baseStart_1289575 : Nat := 118140960795 + 1289575 * 2 ^ 59
def prefixEnd_1289575 : Nat := 4983230072969 + 3 ^ 40 * 1289575 * 2
def baseEnd_1289575 : Nat := 662171815021897265581859

theorem tailTrace_1289575 : CollatzResearch.WordTrace tailWord_1289575 prefixEnd_1289575 662171815021897265581859 := by
  unfold tailWord_1289575
  simp only [CollatzResearch.WordTrace]
  refine ⟨47034664303097491720758179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31356442868731661147172119 47034664303097491720758179)
  ·
    refine ⟨70551996454646237581137269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47034664303097491720758179 70551996454646237581137269)
    ·
      refine ⟨6614249667623084773231619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70551996454646237581137269 6614249667623084773231619)
      ·
        refine ⟨9921374501434627159847429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6614249667623084773231619 9921374501434627159847429)
        ·
          refine ⟨1860257719018992592471393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9921374501434627159847429 1860257719018992592471393)
          ·
            refine ⟨1395193289264244444353545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1860257719018992592471393 1395193289264244444353545)
            ·
              refine ⟨1046394966948183333265159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1395193289264244444353545 1046394966948183333265159)
              ·
                refine ⟨1569592450422274999897739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1046394966948183333265159 1569592450422274999897739)
                ·
                  refine ⟨2354388675633412499846609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1569592450422274999897739 2354388675633412499846609)
                  ·
                    refine ⟨1765791506725059374884957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2354388675633412499846609 1765791506725059374884957)
                    ·
                      refine ⟨662171815021897265581859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1765791506725059374884957 662171815021897265581859)
                      ·
                        rfl

theorem cell23_1289575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_1289575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289575 prefixEnd_1289575 := by exact prefixLift 1289575
  have htrace : WordTrace (prefixWord ++ tailWord_1289575) baseStart_1289575 baseEnd_1289575 := by
    simpa [prefixWord, tailWord_1289575, baseEnd_1289575] using wordTrace_append hprefix tailTrace_1289575
  have hstable : (prefixWord ++ tailWord_1289575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289575).length < 2 ^ (prefixWord ++ tailWord_1289575).sum := by decide
  have hdescent : baseEnd_1289575 < baseStart_1289575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289577 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 1, 5, 4]
def baseStart_1289577 : Nat := 118140960795 + 1289577 * 2 ^ 59
def prefixEnd_1289577 : Nat := 4983230072969 + 3 ^ 40 * 1289577 * 2
def baseEnd_1289577 : Nat := 662172841983206257756849

theorem tailTrace_1289577 : CollatzResearch.WordTrace tailWord_1289577 prefixEnd_1289577 662172841983206257756849 := by
  unfold tailWord_1289577
  simp only [CollatzResearch.WordTrace]
  refine ⟨47034737249090246062330985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31356491499393497374887323 47034737249090246062330985)
  ·
    refine ⟨35276052936817684546748239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47034737249090246062330985 35276052936817684546748239)
    ·
      refine ⟨52914079405226526820122359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35276052936817684546748239 52914079405226526820122359)
      ·
        refine ⟨79371119107839790230183539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52914079405226526820122359 79371119107839790230183539)
        ·
          refine ⟨119056678661759685345275309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79371119107839790230183539 119056678661759685345275309)
          ·
            refine ⟨44646254498159882004478241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119056678661759685345275309 44646254498159882004478241)
            ·
              refine ⟨33484690873619911503358681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44646254498159882004478241 33484690873619911503358681)
              ·
                refine ⟨25113518155214933627519011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33484690873619911503358681 25113518155214933627519011)
                ·
                  refine ⟨37670277232822400441278517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25113518155214933627519011 37670277232822400441278517)
                  ·
                    refine ⟨3531588490577100041369861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37670277232822400441278517 3531588490577100041369861)
                    ·
                      refine ⟨662172841983206257756849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3531588490577100041369861 662172841983206257756849)
                      ·
                        rfl

theorem cell23_1289577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 5, 4].length) (baseStart_1289577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289577 prefixEnd_1289577 := by exact prefixLift 1289577
  have htrace : WordTrace (prefixWord ++ tailWord_1289577) baseStart_1289577 baseEnd_1289577 := by
    simpa [prefixWord, tailWord_1289577, baseEnd_1289577] using wordTrace_append hprefix tailTrace_1289577
  have hstable : (prefixWord ++ tailWord_1289577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289577).length < 2 ^ (prefixWord ++ tailWord_1289577).sum := by decide
  have hdescent : baseEnd_1289577 < baseStart_1289577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289582 : List Nat := [4, 1, 2, 4, 2, 1, 1, 2, 2, 4]
def baseStart_1289582 : Nat := 118140960795 + 1289582 * 2 ^ 59
def prefixEnd_1289582 : Nat := 4983230072969 + 3 ^ 40 * 1289582 * 2
def baseEnd_1289582 : Nat := 220725136462159579398109

theorem tailTrace_1289582 : CollatzResearch.WordTrace tailWord_1289582 prefixEnd_1289582 220725136462159579398109 := by
  unfold tailWord_1289582
  simp only [CollatzResearch.WordTrace]
  refine ⟨5879364951759016489532875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31356613076048087944175333 5879364951759016489532875)
  ·
    refine ⟨8819047427638524734299313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5879364951759016489532875 8819047427638524734299313)
    ·
      refine ⟨6614285570728893550724485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8819047427638524734299313 6614285570728893550724485)
      ·
        refine ⟨1240178544511667540760841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6614285570728893550724485 1240178544511667540760841)
        ·
          refine ⟨930133908383750655570631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1240178544511667540760841 930133908383750655570631)
          ·
            refine ⟨1395200862575625983355947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 930133908383750655570631 1395200862575625983355947)
            ·
              refine ⟨2092801293863438975033921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1395200862575625983355947 2092801293863438975033921)
              ·
                refine ⟨1569600970397579231275441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2092801293863438975033921 1569600970397579231275441)
                ·
                  refine ⟨1177200727798184423456581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1569600970397579231275441 1177200727798184423456581)
                  ·
                    refine ⟨220725136462159579398109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1177200727798184423456581 220725136462159579398109)
                    ·
                      rfl

theorem cell23_1289582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_1289582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289582 prefixEnd_1289582 := by exact prefixLift 1289582
  have htrace : WordTrace (prefixWord ++ tailWord_1289582) baseStart_1289582 baseEnd_1289582 := by
    simpa [prefixWord, tailWord_1289582, baseEnd_1289582] using wordTrace_append hprefix tailTrace_1289582
  have hstable : (prefixWord ++ tailWord_1289582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289582).length < 2 ^ (prefixWord ++ tailWord_1289582).sum := by decide
  have hdescent : baseEnd_1289582 < baseStart_1289582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289604 : List Nat := [2, 3, 2, 1, 1, 3, 2, 1, 2, 6]
def baseStart_1289604 : Nat := 118140960795 + 1289604 * 2 ^ 59
def prefixEnd_1289604 : Nat := 4983230072969 + 3 ^ 40 * 1289604 * 2
def baseEnd_1289604 : Nat := 220728901986959217373075

theorem tailTrace_1289604 : CollatzResearch.WordTrace tailWord_1289604 prefixEnd_1289604 220728901986959217373075 := by
  unfold tailWord_1289604
  simp only [CollatzResearch.WordTrace]
  refine ⟨23517861009996214836781933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31357148013328286449042577 23517861009996214836781933)
  ·
    refine ⟨8819197878748580563793225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23517861009996214836781933 8819197878748580563793225)
    ·
      refine ⟨6614398409061435422844919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8819197878748580563793225 6614398409061435422844919)
      ·
        refine ⟨9921597613592153134267379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6614398409061435422844919 9921597613592153134267379)
        ·
          refine ⟨14882396420388229701401069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9921597613592153134267379 14882396420388229701401069)
          ·
            refine ⟨5580898657645586138025401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14882396420388229701401069 5580898657645586138025401)
            ·
              refine ⟨4185673993234189603519051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5580898657645586138025401 4185673993234189603519051)
              ·
                refine ⟨6278510989851284405278577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4185673993234189603519051 6278510989851284405278577)
                ·
                  refine ⟨4708883242388463303958933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6278510989851284405278577 4708883242388463303958933)
                  ·
                    refine ⟨220728901986959217373075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4708883242388463303958933 220728901986959217373075)
                    ·
                      rfl

theorem cell23_1289604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_1289604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289604 prefixEnd_1289604 := by exact prefixLift 1289604
  have htrace : WordTrace (prefixWord ++ tailWord_1289604) baseStart_1289604 baseEnd_1289604 := by
    simpa [prefixWord, tailWord_1289604, baseEnd_1289604] using wordTrace_append hprefix tailTrace_1289604
  have hstable : (prefixWord ++ tailWord_1289604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289604).length < 2 ^ (prefixWord ++ tailWord_1289604).sum := by decide
  have hdescent : baseEnd_1289604 < baseStart_1289604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289644 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 3]
def baseStart_1289644 : Nat := 118140960795 + 1289644 * 2 ^ 59
def prefixEnd_1289644 : Nat := 4983230072969 + 3 ^ 40 * 1289644 * 2
def baseEnd_1289644 : Nat := 662207245187057495619041

theorem tailTrace_1289644 : CollatzResearch.WordTrace tailWord_1289644 prefixEnd_1289644 662207245187057495619041 := by
  unfold tailWord_1289644
  simp only [CollatzResearch.WordTrace]
  refine ⟨23518590469923758252509993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31358120626565011003346657 23518590469923758252509993)
  ·
    refine ⟨17638942852442818689382495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23518590469923758252509993 17638942852442818689382495)
    ·
      refine ⟨26458414278664228034073743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17638942852442818689382495 26458414278664228034073743)
      ·
        refine ⟨39687621417996342051110615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26458414278664228034073743 39687621417996342051110615)
        ·
          refine ⟨59531432126994513076665923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39687621417996342051110615 59531432126994513076665923)
          ·
            refine ⟨89297148190491769614998885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59531432126994513076665923 89297148190491769614998885)
            ·
              refine ⟨16743215285717206802812291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89297148190491769614998885 16743215285717206802812291)
              ·
                refine ⟨25114822928575810204218437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16743215285717206802812291 25114822928575810204218437)
                ·
                  refine ⟨4709029299107964413290957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25114822928575810204218437 4709029299107964413290957)
                  ·
                    refine ⟨1765885987165486654984109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4709029299107964413290957 1765885987165486654984109)
                    ·
                      refine ⟨662207245187057495619041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1765885987165486654984109 662207245187057495619041)
                      ·
                        rfl

theorem cell23_1289644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 3].length) (baseStart_1289644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289644 prefixEnd_1289644 := by exact prefixLift 1289644
  have htrace : WordTrace (prefixWord ++ tailWord_1289644) baseStart_1289644 baseEnd_1289644 := by
    simpa [prefixWord, tailWord_1289644, baseEnd_1289644] using wordTrace_append hprefix tailTrace_1289644
  have hstable : (prefixWord ++ tailWord_1289644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289644).length < 2 ^ (prefixWord ++ tailWord_1289644).sum := by decide
  have hdescent : baseEnd_1289644 < baseStart_1289644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289645 : List Nat := [1, 5, 2, 2, 1, 1, 2, 1, 4, 2, 2]
def baseStart_1289645 : Nat := 118140960795 + 1289645 * 2 ^ 59
def prefixEnd_1289645 : Nat := 4983230072969 + 3 ^ 40 * 1289645 * 2
def baseEnd_1289645 : Nat := 662207758667711991706537

theorem tailTrace_1289645 : CollatzResearch.WordTrace tailWord_1289645 prefixEnd_1289645 662207758667711991706537 := by
  unfold tailWord_1289645
  simp only [CollatzResearch.WordTrace]
  refine ⟨47037217412843893675806389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31358144941895929117204259 47037217412843893675806389)
  ·
    refine ⟨4409739132454115032106849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47037217412843893675806389 4409739132454115032106849)
    ·
      refine ⟨3307304349340586274080137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4409739132454115032106849 3307304349340586274080137)
      ·
        refine ⟨2480478262005439705560103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3307304349340586274080137 2480478262005439705560103)
        ·
          refine ⟨3720717393008159558340155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2480478262005439705560103 3720717393008159558340155)
          ·
            refine ⟨5581076089512239337510233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3720717393008159558340155 5581076089512239337510233)
            ·
              refine ⟨4185807067134179503132675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5581076089512239337510233 4185807067134179503132675)
              ·
                refine ⟨6278710600701269254699013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4185807067134179503132675 6278710600701269254699013)
                ·
                  refine ⟨1177258237631487985256065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6278710600701269254699013 1177258237631487985256065)
                  ·
                    refine ⟨882943678223615988942049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1177258237631487985256065 882943678223615988942049)
                    ·
                      refine ⟨662207758667711991706537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 882943678223615988942049 662207758667711991706537)
                      ·
                        rfl

theorem cell23_1289645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_1289645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289645 prefixEnd_1289645 := by exact prefixLift 1289645
  have htrace : WordTrace (prefixWord ++ tailWord_1289645) baseStart_1289645 baseEnd_1289645 := by
    simpa [prefixWord, tailWord_1289645, baseEnd_1289645] using wordTrace_append hprefix tailTrace_1289645
  have hstable : (prefixWord ++ tailWord_1289645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289645).length < 2 ^ (prefixWord ++ tailWord_1289645).sum := by decide
  have hdescent : baseEnd_1289645 < baseStart_1289645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289704 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_1289704 : Nat := 118140960795 + 1289704 * 2 ^ 59
def prefixEnd_1289704 : Nat := 4983230072969 + 3 ^ 40 * 1289704 * 2
def baseEnd_1289704 : Nat := 662238054026327260868765

theorem tailTrace_1289704 : CollatzResearch.WordTrace tailWord_1289704 prefixEnd_1289704 662238054026327260868765 := by
  unfold tailWord_1289704
  simp only [CollatzResearch.WordTrace]
  refine ⟨23519684659815073376102083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31359579546420097834802777 23519684659815073376102083)
  ·
    refine ⟨35279526989722610064153125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23519684659815073376102083 35279526989722610064153125)
    ·
      refine ⟨6614911310572989387028711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35279526989722610064153125 6614911310572989387028711)
      ·
        refine ⟨9922366965859484080543067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6614911310572989387028711 9922366965859484080543067)
        ·
          refine ⟨14883550448789226120814601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9922366965859484080543067 14883550448789226120814601)
          ·
            refine ⟨11162662836591919590610951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14883550448789226120814601 11162662836591919590610951)
            ·
              refine ⟨16743994254887879385916427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11162662836591919590610951 16743994254887879385916427)
              ·
                refine ⟨25115991382331819078874641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16743994254887879385916427 25115991382331819078874641)
                ·
                  refine ⟨18836993536748864309155981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25115991382331819078874641 18836993536748864309155981)
                  ·
                    refine ⟨7063872576280824115933493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18836993536748864309155981 7063872576280824115933493)
                    ·
                      refine ⟨662238054026327260868765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7063872576280824115933493 662238054026327260868765)
                      ·
                        rfl

theorem cell23_1289704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_1289704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289704 prefixEnd_1289704 := by exact prefixLift 1289704
  have htrace : WordTrace (prefixWord ++ tailWord_1289704) baseStart_1289704 baseEnd_1289704 := by
    simpa [prefixWord, tailWord_1289704, baseEnd_1289704] using wordTrace_append hprefix tailTrace_1289704
  have hstable : (prefixWord ++ tailWord_1289704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289704).length < 2 ^ (prefixWord ++ tailWord_1289704).sum := by decide
  have hdescent : baseEnd_1289704 < baseStart_1289704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289718 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2]
def baseStart_1289718 : Nat := 118140960795 + 1289718 * 2 ^ 59
def prefixEnd_1289718 : Nat := 4983230072969 + 3 ^ 40 * 1289718 * 2
def baseEnd_1289718 : Nat := 662245242755490206093701

theorem tailTrace_1289718 : CollatzResearch.WordTrace tailWord_1289718 prefixEnd_1289718 662245242755490206093701 := by
  unfold tailWord_1289718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2939992496348714196450863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31359919961052951428809205 2939992496348714196450863)
  ·
    refine ⟨4409988744523071294676295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2939992496348714196450863 4409988744523071294676295)
    ·
      refine ⟨6614983116784606942014443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4409988744523071294676295 6614983116784606942014443)
      ·
        refine ⟨9922474675176910413021665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6614983116784606942014443 9922474675176910413021665)
        ·
          refine ⟨7441856006382682809766249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9922474675176910413021665 7441856006382682809766249)
          ·
            refine ⟨5581392004787012107324687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7441856006382682809766249 5581392004787012107324687)
            ·
              refine ⟨8372088007180518160987031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5581392004787012107324687 8372088007180518160987031)
              ·
                refine ⟨12558132010770777241480547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8372088007180518160987031 12558132010770777241480547)
                ·
                  refine ⟨18837198016156165862220821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12558132010770777241480547 18837198016156165862220821)
                  ·
                    refine ⟨882993657007320274791601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18837198016156165862220821 882993657007320274791601)
                    ·
                      refine ⟨662245242755490206093701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 882993657007320274791601 662245242755490206093701)
                      ·
                        rfl

theorem cell23_1289718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_1289718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289718 prefixEnd_1289718 := by exact prefixLift 1289718
  have htrace : WordTrace (prefixWord ++ tailWord_1289718) baseStart_1289718 baseEnd_1289718 := by
    simpa [prefixWord, tailWord_1289718, baseEnd_1289718] using wordTrace_append hprefix tailTrace_1289718
  have hstable : (prefixWord ++ tailWord_1289718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289718).length < 2 ^ (prefixWord ++ tailWord_1289718).sum := by decide
  have hdescent : baseEnd_1289718 < baseStart_1289718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289738 : List Nat := [3, 1, 2, 2, 2, 2, 3, 1, 2, 2, 3]
def baseStart_1289738 : Nat := 118140960795 + 1289738 * 2 ^ 59
def prefixEnd_1289738 : Nat := 4983230072969 + 3 ^ 40 * 1289738 * 2
def baseEnd_1289738 : Nat := 662255512368580127843609

theorem tailTrace_1289738 : CollatzResearch.WordTrace tailWord_1289738 prefixEnd_1289738 662255512368580127843609 := by
  unfold tailWord_1289738
  simp only [CollatzResearch.WordTrace]
  refine ⟨11760152350376742639735467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31360406267671313705961245 11760152350376742639735467)
  ·
    refine ⟨17640228525565113959603201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11760152350376742639735467 17640228525565113959603201)
    ·
      refine ⟨13230171394173835469702401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17640228525565113959603201 13230171394173835469702401)
      ·
        refine ⟨9922628545630376602276801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13230171394173835469702401 9922628545630376602276801)
        ·
          refine ⟨7441971409222782451707601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9922628545630376602276801 7441971409222782451707601)
          ·
            refine ⟨5581478556917086838780701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7441971409222782451707601 5581478556917086838780701)
            ·
              refine ⟨2093054458843907564542763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5581478556917086838780701 2093054458843907564542763)
              ·
                refine ⟨3139581688265861346814145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2093054458843907564542763 3139581688265861346814145)
                ·
                  refine ⟨2354686266199396010110609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3139581688265861346814145 2354686266199396010110609)
                  ·
                    refine ⟨1766014699649547007582957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2354686266199396010110609 1766014699649547007582957)
                    ·
                      refine ⟨662255512368580127843609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1766014699649547007582957 662255512368580127843609)
                      ·
                        rfl

theorem cell23_1289738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_1289738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289738 prefixEnd_1289738 := by exact prefixLift 1289738
  have htrace : WordTrace (prefixWord ++ tailWord_1289738) baseStart_1289738 baseEnd_1289738 := by
    simpa [prefixWord, tailWord_1289738, baseEnd_1289738] using wordTrace_append hprefix tailTrace_1289738
  have hstable : (prefixWord ++ tailWord_1289738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289738).length < 2 ^ (prefixWord ++ tailWord_1289738).sum := by decide
  have hdescent : baseEnd_1289738 < baseStart_1289738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289841 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 5, 3, 3]
def baseStart_1289841 : Nat := 118140960795 + 1289841 * 2 ^ 59
def prefixEnd_1289841 : Nat := 4983230072969 + 3 ^ 40 * 1289841 * 2
def baseEnd_1289841 : Nat := 662308400875993224855635

theorem tailTrace_1289841 : CollatzResearch.WordTrace tailWord_1289841 prefixEnd_1289841 662308400875993224855635 := by
  unfold tailWord_1289841
  simp only [CollatzResearch.WordTrace]
  refine ⟨47044366120133819149941377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31362910746755879433294251 47044366120133819149941377)
  ·
    refine ⟨35283274590100364362456033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47044366120133819149941377 35283274590100364362456033)
    ·
      refine ⟨26462455942575273271842025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35283274590100364362456033 26462455942575273271842025)
      ·
        refine ⟨19846841956931454953881519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26462455942575273271842025 19846841956931454953881519)
        ·
          refine ⟨29770262935397182430822279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19846841956931454953881519 29770262935397182430822279)
          ·
            refine ⟨44655394403095773646233419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29770262935397182430822279 44655394403095773646233419)
            ·
              refine ⟨66983091604643660469350129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44655394403095773646233419 66983091604643660469350129)
              ·
                refine ⟨50237318703482745352012597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66983091604643660469350129 50237318703482745352012597)
                ·
                  refine ⟨4709748628451507376751181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50237318703482745352012597 4709748628451507376751181)
                  ·
                    refine ⟨1766155735669315266281693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4709748628451507376751181 1766155735669315266281693)
                    ·
                      refine ⟨662308400875993224855635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1766155735669315266281693 662308400875993224855635)
                      ·
                        rfl

theorem cell23_1289841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_1289841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289841 prefixEnd_1289841 := by exact prefixLift 1289841
  have htrace : WordTrace (prefixWord ++ tailWord_1289841) baseStart_1289841 baseEnd_1289841 := by
    simpa [prefixWord, tailWord_1289841, baseEnd_1289841] using wordTrace_append hprefix tailTrace_1289841
  have hstable : (prefixWord ++ tailWord_1289841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289841).length < 2 ^ (prefixWord ++ tailWord_1289841).sum := by decide
  have hdescent : baseEnd_1289841 < baseStart_1289841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289845 : List Nat := [1, 3, 4, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_1289845 : Nat := 118140960795 + 1289845 * 2 ^ 59
def prefixEnd_1289845 : Nat := 4983230072969 + 3 ^ 40 * 1289845 * 2
def baseEnd_1289845 : Nat := 662310454798611209205617

theorem tailTrace_1289845 : CollatzResearch.WordTrace tailWord_1289845 prefixEnd_1289845 662310454798611209205617 := by
  unfold tailWord_1289845
  simp only [CollatzResearch.WordTrace]
  refine ⟨47044512012119327833086989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31363008008079551888724659 47044512012119327833086989)
  ·
    refine ⟨17641692004544747937407621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47044512012119327833086989 17641692004544747937407621)
    ·
      refine ⟨3307817250852140238263929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17641692004544747937407621 3307817250852140238263929)
      ·
        refine ⟨2480862938139105178697947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3307817250852140238263929 2480862938139105178697947)
        ·
          refine ⟨3721294407208657768046921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2480862938139105178697947 3721294407208657768046921)
          ·
            refine ⟨2790970805406493326035191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3721294407208657768046921 2790970805406493326035191)
            ·
              refine ⟨4186456208109739989052787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2790970805406493326035191 4186456208109739989052787)
              ·
                refine ⟨6279684312164609983579181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4186456208109739989052787 6279684312164609983579181)
                ·
                  refine ⟨2354881617061728743842193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6279684312164609983579181 2354881617061728743842193)
                  ·
                    refine ⟨1766161212796296557881645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2354881617061728743842193 1766161212796296557881645)
                    ·
                      refine ⟨662310454798611209205617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1766161212796296557881645 662310454798611209205617)
                      ·
                        rfl

theorem cell23_1289845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_1289845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289845 prefixEnd_1289845 := by exact prefixLift 1289845
  have htrace : WordTrace (prefixWord ++ tailWord_1289845) baseStart_1289845 baseEnd_1289845 := by
    simpa [prefixWord, tailWord_1289845, baseEnd_1289845] using wordTrace_append hprefix tailTrace_1289845
  have hstable : (prefixWord ++ tailWord_1289845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289845).length < 2 ^ (prefixWord ++ tailWord_1289845).sum := by decide
  have hdescent : baseEnd_1289845 < baseStart_1289845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289876 : List Nat := [2, 4, 2, 2, 2, 1, 1, 4, 1, 2, 2]
def baseStart_1289876 : Nat := 118140960795 + 1289876 * 2 ^ 59
def prefixEnd_1289876 : Nat := 4983230072969 + 3 ^ 40 * 1289876 * 2
def baseEnd_1289876 : Nat := 662326372698900587917975

theorem tailTrace_1289876 : CollatzResearch.WordTrace tailWord_1289876 prefixEnd_1289876 662326372698900587917975 := by
  unfold tailWord_1289876
  simp only [CollatzResearch.WordTrace]
  refine ⟨23522821337503510063732741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31363761783338013418310321 23522821337503510063732741)
  ·
    refine ⟨4410529000781908136949889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23522821337503510063732741 4410529000781908136949889)
    ·
      refine ⟨3307896750586431102712417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4410529000781908136949889 3307896750586431102712417)
      ·
        refine ⟨2480922562939823327034313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3307896750586431102712417 2480922562939823327034313)
        ·
          refine ⟨1860691922204867495275735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2480922562939823327034313 1860691922204867495275735)
          ·
            refine ⟨2791037883307301242913603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1860691922204867495275735 2791037883307301242913603)
            ·
              refine ⟨4186556824960951864370405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2791037883307301242913603 4186556824960951864370405)
              ·
                refine ⟨784979404680178474569451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4186556824960951864370405 784979404680178474569451)
                ·
                  refine ⟨1177469107020267711854177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 784979404680178474569451 1177469107020267711854177)
                  ·
                    refine ⟨883101830265200783890633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1177469107020267711854177 883101830265200783890633)
                    ·
                      refine ⟨662326372698900587917975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 883101830265200783890633 662326372698900587917975)
                      ·
                        rfl

theorem cell23_1289876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_1289876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289876 prefixEnd_1289876 := by exact prefixLift 1289876
  have htrace : WordTrace (prefixWord ++ tailWord_1289876) baseStart_1289876 baseEnd_1289876 := by
    simpa [prefixWord, tailWord_1289876, baseEnd_1289876] using wordTrace_append hprefix tailTrace_1289876
  have hstable : (prefixWord ++ tailWord_1289876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289876).length < 2 ^ (prefixWord ++ tailWord_1289876).sum := by decide
  have hdescent : baseEnd_1289876 < baseStart_1289876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289891 : List Nat := [1, 1, 1, 4, 1, 1, 5, 1, 2, 6]
def baseStart_1289891 : Nat := 118140960795 + 1289891 * 2 ^ 59
def prefixEnd_1289891 : Nat := 4983230072969 + 3 ^ 40 * 1289891 * 2
def baseEnd_1289891 : Nat := 220778024969572676410135

theorem tailTrace_1289891 : CollatzResearch.WordTrace tailWord_1289891 prefixEnd_1289891 220778024969572676410135 := by
  unfold tailWord_1289891
  simp only [CollatzResearch.WordTrace]
  refine ⟨47046189769952677689261527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31364126513301785126174351 47046189769952677689261527)
  ·
    refine ⟨70569284654929016533892291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47046189769952677689261527 70569284654929016533892291)
    ·
      refine ⟨105853926982393524800838437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70569284654929016533892291 105853926982393524800838437)
      ·
        refine ⟨19847611309198785900157207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105853926982393524800838437 19847611309198785900157207)
        ·
          refine ⟨29771416963798178850235811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19847611309198785900157207 29771416963798178850235811)
          ·
            refine ⟨44657125445697268275353717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29771416963798178850235811 44657125445697268275353717)
            ·
              refine ⟨4186605510534118900814411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44657125445697268275353717 4186605510534118900814411)
              ·
                refine ⟨6279908265801178351221617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4186605510534118900814411 6279908265801178351221617)
                ·
                  refine ⟨4709931199350883763416213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6279908265801178351221617 4709931199350883763416213)
                  ·
                    refine ⟨220778024969572676410135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4709931199350883763416213 220778024969572676410135)
                    ·
                      rfl

theorem cell23_1289891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 6].length) (baseStart_1289891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289891 prefixEnd_1289891 := by exact prefixLift 1289891
  have htrace : WordTrace (prefixWord ++ tailWord_1289891) baseStart_1289891 baseEnd_1289891 := by
    simpa [prefixWord, tailWord_1289891, baseEnd_1289891] using wordTrace_append hprefix tailTrace_1289891
  have hstable : (prefixWord ++ tailWord_1289891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289891).length < 2 ^ (prefixWord ++ tailWord_1289891).sum := by decide
  have hdescent : baseEnd_1289891 < baseStart_1289891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289926 : List Nat := [6, 1, 2, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_1289926 : Nat := 118140960795 + 1289926 * 2 ^ 59
def prefixEnd_1289926 : Nat := 4983230072969 + 3 ^ 40 * 1289926 * 2
def baseEnd_1289926 : Nat := 662352046731625392292745

theorem tailTrace_1289926 : CollatzResearch.WordTrace tailWord_1289926 prefixEnd_1289926 662352046731625392292745 := by
  unfold tailWord_1289926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1470233322650808708337051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31364977549883919111190421 1470233322650808708337051)
  ·
    refine ⟨2205349983976213062505577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1470233322650808708337051 2205349983976213062505577)
    ·
      refine ⟨1654012487982159796879183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2205349983976213062505577 1654012487982159796879183)
      ·
        refine ⟨2481018731973239695318775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1654012487982159796879183 2481018731973239695318775)
        ·
          refine ⟨3721528097959859542978163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2481018731973239695318775 3721528097959859542978163)
          ·
            refine ⟨5582292146939789314467245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3721528097959859542978163 5582292146939789314467245)
            ·
              refine ⟨2093359555102420992925217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5582292146939789314467245 2093359555102420992925217)
              ·
                refine ⟨1570019666326815744693913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2093359555102420992925217 1570019666326815744693913)
                ·
                  refine ⟨1177514749745111808520435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1570019666326815744693913 1177514749745111808520435)
                  ·
                    refine ⟨1766272124617667712780653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1177514749745111808520435 1766272124617667712780653)
                    ·
                      refine ⟨662352046731625392292745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1766272124617667712780653 662352046731625392292745)
                      ·
                        rfl

theorem cell23_1289926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_1289926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289926 prefixEnd_1289926 := by exact prefixLift 1289926
  have htrace : WordTrace (prefixWord ++ tailWord_1289926) baseStart_1289926 baseEnd_1289926 := by
    simpa [prefixWord, tailWord_1289926, baseEnd_1289926] using wordTrace_append hprefix tailTrace_1289926
  have hstable : (prefixWord ++ tailWord_1289926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289926).length < 2 ^ (prefixWord ++ tailWord_1289926).sum := by decide
  have hdescent : baseEnd_1289926 < baseStart_1289926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289938 : List Nat := [3, 2, 2, 2, 2, 1, 1, 3, 7]
def baseStart_1289938 : Nat := 118140960795 + 1289938 * 2 ^ 59
def prefixEnd_1289938 : Nat := 4983230072969 + 3 ^ 40 * 1289938 * 2
def baseEnd_1289938 : Nat := 73595356499942149482521

theorem tailTrace_1289938 : CollatzResearch.WordTrace tailWord_1289938 prefixEnd_1289938 73595356499942149482521 := by
  unfold tailWord_1289938
  simp only [CollatzResearch.WordTrace]
  refine ⟨11761976000195601179055617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31365269333854936477481645 11761976000195601179055617)
  ·
    refine ⟨8821482000146700884291713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11761976000195601179055617 8821482000146700884291713)
    ·
      refine ⟨6616111500110025663218785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8821482000146700884291713 6616111500110025663218785)
      ·
        refine ⟨4962083625082519247414089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6616111500110025663218785 4962083625082519247414089)
        ·
          refine ⟨3721562718811889435560567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4962083625082519247414089 3721562718811889435560567)
          ·
            refine ⟨5582344078217834153340851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3721562718811889435560567 5582344078217834153340851)
            ·
              refine ⟨8373516117326751230011277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5582344078217834153340851 8373516117326751230011277)
              ·
                refine ⟨3140068543997531711254229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8373516117326751230011277 3140068543997531711254229)
                ·
                  refine ⟨73595356499942149482521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3140068543997531711254229 73595356499942149482521)
                  ·
                    rfl

theorem cell23_1289938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 7].length) (baseStart_1289938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289938 prefixEnd_1289938 := by exact prefixLift 1289938
  have htrace : WordTrace (prefixWord ++ tailWord_1289938) baseStart_1289938 baseEnd_1289938 := by
    simpa [prefixWord, tailWord_1289938, baseEnd_1289938] using wordTrace_append hprefix tailTrace_1289938
  have hstable : (prefixWord ++ tailWord_1289938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289938).length < 2 ^ (prefixWord ++ tailWord_1289938).sum := by decide
  have hdescent : baseEnd_1289938 < baseStart_1289938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289951 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 3, 7]
def baseStart_1289951 : Nat := 118140960795 + 1289951 * 2 ^ 59
def prefixEnd_1289951 : Nat := 4983230072969 + 3 ^ 40 * 1289951 * 2
def baseEnd_1289951 : Nat := 220788294582662598160043

theorem tailTrace_1289951 : CollatzResearch.WordTrace tailWord_1289951 prefixEnd_1289951 220788294582662598160043 := by
  unfold tailWord_1289951
  simp only [CollatzResearch.WordTrace]
  refine ⟨47048378149735307936445707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31365585433156871957630471 47048378149735307936445707)
  ·
    refine ⟨70572567224602961904668561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47048378149735307936445707 70572567224602961904668561)
    ·
      refine ⟨52929425418452221428501421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70572567224602961904668561 52929425418452221428501421)
      ·
        refine ⟨19848534531919583035688033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52929425418452221428501421 19848534531919583035688033)
        ·
          refine ⟨14886400898939687276766025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19848534531919583035688033 14886400898939687276766025)
          ·
            refine ⟨11164800674204765457574519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14886400898939687276766025 11164800674204765457574519)
            ·
              refine ⟨16747201011307148186361779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11164800674204765457574519 16747201011307148186361779)
              ·
                refine ⟨25120801516960722279542669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16747201011307148186361779 25120801516960722279542669)
                ·
                  refine ⟨9420300568860270854828501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25120801516960722279542669 9420300568860270854828501)
                  ·
                    refine ⟨220788294582662598160043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9420300568860270854828501 220788294582662598160043)
                    ·
                      rfl

theorem cell23_1289951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 7].length) (baseStart_1289951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289951 prefixEnd_1289951 := by exact prefixLift 1289951
  have htrace : WordTrace (prefixWord ++ tailWord_1289951) baseStart_1289951 baseEnd_1289951 := by
    simpa [prefixWord, tailWord_1289951, baseEnd_1289951] using wordTrace_append hprefix tailTrace_1289951
  have hstable : (prefixWord ++ tailWord_1289951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289951).length < 2 ^ (prefixWord ++ tailWord_1289951).sum := by decide
  have hdescent : baseEnd_1289951 < baseStart_1289951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289961 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 3, 2, 5]
def baseStart_1289961 : Nat := 118140960795 + 1289961 * 2 ^ 59
def prefixEnd_1289961 : Nat := 4983230072969 + 3 ^ 40 * 1289961 * 2
def baseEnd_1289961 : Nat := 662370018554532755355083

theorem tailTrace_1289961 : CollatzResearch.WordTrace tailWord_1289961 prefixEnd_1289961 662370018554532755355083 := by
  unfold tailWord_1289961
  simp only [CollatzResearch.WordTrace]
  refine ⟨47048742879699079644309737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31365828586466053096206491 47048742879699079644309737)
  ·
    refine ⟨35286557159774309733232303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47048742879699079644309737 35286557159774309733232303)
    ·
      refine ⟨52929835739661464599848455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35286557159774309733232303 52929835739661464599848455)
      ·
        refine ⟨79394753609492196899772683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52929835739661464599848455 79394753609492196899772683)
        ·
          refine ⟨119092130414238295349659025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79394753609492196899772683 119092130414238295349659025)
          ·
            refine ⟨89319097810678721512244269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119092130414238295349659025 89319097810678721512244269)
            ·
              refine ⟨33494661679004520567091601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89319097810678721512244269 33494661679004520567091601)
              ·
                refine ⟨25120996259253390425318701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33494661679004520567091601 25120996259253390425318701)
                ·
                  refine ⟨9420373597220021409494513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25120996259253390425318701 9420373597220021409494513)
                  ·
                    refine ⟨7065280197915016057120885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9420373597220021409494513 7065280197915016057120885)
                    ·
                      refine ⟨662370018554532755355083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7065280197915016057120885 662370018554532755355083)
                      ·
                        rfl

theorem cell23_1289961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 2, 5].length) (baseStart_1289961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289961 prefixEnd_1289961 := by exact prefixLift 1289961
  have htrace : WordTrace (prefixWord ++ tailWord_1289961) baseStart_1289961 baseEnd_1289961 := by
    simpa [prefixWord, tailWord_1289961, baseEnd_1289961] using wordTrace_append hprefix tailTrace_1289961
  have hstable : (prefixWord ++ tailWord_1289961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289961).length < 2 ^ (prefixWord ++ tailWord_1289961).sum := by decide
  have hdescent : baseEnd_1289961 < baseStart_1289961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290008 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 3, 4, 3]
def baseStart_1290008 : Nat := 118140960795 + 1290008 * 2 ^ 59
def prefixEnd_1290008 : Nat := 4983230072969 + 3 ^ 40 * 1290008 * 2
def baseEnd_1290008 : Nat := 662394152145294071467367

theorem tailTrace_1290008 : CollatzResearch.WordTrace tailWord_1290008 prefixEnd_1290008 662394152145294071467367 := by
  unfold tailWord_1290008
  simp only [CollatzResearch.WordTrace]
  refine ⟨23525228555264403335635339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31366971407019204447513785 23525228555264403335635339)
  ·
    refine ⟨35287842832896605003453009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23525228555264403335635339 35287842832896605003453009)
    ·
      refine ⟨26465882124672453752589757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35287842832896605003453009 26465882124672453752589757)
      ·
        refine ⟨9924705796752170157221159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26465882124672453752589757 9924705796752170157221159)
        ·
          refine ⟨14887058695128255235831739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9924705796752170157221159 14887058695128255235831739)
          ·
            refine ⟨22330588042692382853747609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14887058695128255235831739 22330588042692382853747609)
            ·
              refine ⟨16747941032019287140310707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22330588042692382853747609 16747941032019287140310707)
              ·
                refine ⟨25121911548028930710466061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16747941032019287140310707 25121911548028930710466061)
                ·
                  refine ⟨9420716830510849016424773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25121911548028930710466061 9420716830510849016424773)
                  ·
                    refine ⟨1766384405720784190579645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9420716830510849016424773 1766384405720784190579645)
                    ·
                      refine ⟨662394152145294071467367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1766384405720784190579645 662394152145294071467367)
                      ·
                        rfl

theorem cell23_1290008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_1290008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290008 prefixEnd_1290008 := by exact prefixLift 1290008
  have htrace : WordTrace (prefixWord ++ tailWord_1290008) baseStart_1290008 baseEnd_1290008 := by
    simpa [prefixWord, tailWord_1290008, baseEnd_1290008] using wordTrace_append hprefix tailTrace_1290008
  have hstable : (prefixWord ++ tailWord_1290008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290008).length < 2 ^ (prefixWord ++ tailWord_1290008).sum := by decide
  have hdescent : baseEnd_1290008 < baseStart_1290008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290045 : List Nat := [1, 4, 1, 4, 1, 1, 1, 4, 6]
def baseStart_1290045 : Nat := 118140960795 + 1290045 * 2 ^ 59
def prefixEnd_1290045 : Nat := 4983230072969 + 3 ^ 40 * 1290045 * 2
def baseEnd_1290045 : Nat := 73601461214390047411633

theorem tailTrace_1290045 : CollatzResearch.WordTrace tailWord_1290045 prefixEnd_1290045 73601461214390047411633 := by
  unfold tailWord_1290045
  simp only [CollatzResearch.WordTrace]
  refine ⟨47051806611394761990367589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31367871074263174660245059 47051806611394761990367589)
  ·
    refine ⟨8822213739636517873193923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47051806611394761990367589 8822213739636517873193923)
    ·
      refine ⟨13233320609454776809790885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8822213739636517873193923 13233320609454776809790885)
      ·
        refine ⟨2481247614272770651835791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13233320609454776809790885 2481247614272770651835791)
        ·
          refine ⟨3721871421409155977753687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2481247614272770651835791 3721871421409155977753687)
          ·
            refine ⟨5582807132113733966630531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3721871421409155977753687 5582807132113733966630531)
            ·
              refine ⟨8374210698170600949945797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5582807132113733966630531 8374210698170600949945797)
              ·
                refine ⟨1570164505906987678114837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8374210698170600949945797 1570164505906987678114837)
                ·
                  refine ⟨73601461214390047411633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1570164505906987678114837 73601461214390047411633)
                  ·
                    rfl

theorem cell23_1290045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 6].length) (baseStart_1290045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290045 prefixEnd_1290045 := by exact prefixLift 1290045
  have htrace : WordTrace (prefixWord ++ tailWord_1290045) baseStart_1290045 baseEnd_1290045 := by
    simpa [prefixWord, tailWord_1290045, baseEnd_1290045] using wordTrace_append hprefix tailTrace_1290045
  have hstable : (prefixWord ++ tailWord_1290045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290045).length < 2 ^ (prefixWord ++ tailWord_1290045).sum := by decide
  have hdescent : baseEnd_1290045 < baseStart_1290045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290058 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 5, 5]
def baseStart_1290058 : Nat := 118140960795 + 1290058 * 2 ^ 59
def prefixEnd_1290058 : Nat := 4983230072969 + 3 ^ 40 * 1290058 * 2
def baseEnd_1290058 : Nat := 220806608726006291947379

theorem tailTrace_1290058 : CollatzResearch.WordTrace tailWord_1290058 prefixEnd_1290058 220806608726006291947379 := by
  unfold tailWord_1290058
  simp only [CollatzResearch.WordTrace]
  refine ⟨11763070190086916302647707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31368187173565110140393885 11763070190086916302647707)
  ·
    refine ⟨17644605285130374453971561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11763070190086916302647707 17644605285130374453971561)
    ·
      refine ⟨13233453963847780840478671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17644605285130374453971561 13233453963847780840478671)
      ·
        refine ⟨19850180945771671260718007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13233453963847780840478671 19850180945771671260718007)
        ·
          refine ⟨29775271418657506891077011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19850180945771671260718007 29775271418657506891077011)
          ·
            refine ⟨44662907127986260336615517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29775271418657506891077011 44662907127986260336615517)
            ·
              refine ⟨16748590172994847626230819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44662907127986260336615517 16748590172994847626230819)
              ·
                refine ⟨25122885259492271439346229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16748590172994847626230819 25122885259492271439346229)
                ·
                  refine ⟨2355270493077400447438709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25122885259492271439346229 2355270493077400447438709)
                  ·
                    refine ⟨220806608726006291947379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2355270493077400447438709 220806608726006291947379)
                    ·
                      rfl

theorem cell23_1290058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_1290058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290058 prefixEnd_1290058 := by exact prefixLift 1290058
  have htrace : WordTrace (prefixWord ++ tailWord_1290058) baseStart_1290058 baseEnd_1290058 := by
    simpa [prefixWord, tailWord_1290058, baseEnd_1290058] using wordTrace_append hprefix tailTrace_1290058
  have hstable : (prefixWord ++ tailWord_1290058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290058).length < 2 ^ (prefixWord ++ tailWord_1290058).sum := by decide
  have hdescent : baseEnd_1290058 < baseStart_1290058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290076 : List Nat := [2, 2, 4, 2, 3, 1, 1, 1, 2, 2, 3]
def baseStart_1290076 : Nat := 118140960795 + 1290076 * 2 ^ 59
def prefixEnd_1290076 : Nat := 4983230072969 + 3 ^ 40 * 1290076 * 2
def baseEnd_1290076 : Nat := 662429068829799805417055

theorem tailTrace_1290076 : CollatzResearch.WordTrace tailWord_1290076 prefixEnd_1290076 662429068829799805417055 := by
  unfold tailWord_1290076
  simp only [CollatzResearch.WordTrace]
  refine ⟨23526468637141227142373041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31368624849521636189830721 23526468637141227142373041)
  ·
    refine ⟨17644851477855920356779781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23526468637141227142373041 17644851477855920356779781)
    ·
      refine ⟨3308409652097985066896209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17644851477855920356779781 3308409652097985066896209)
      ·
        refine ⟨2481307239073488800172157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3308409652097985066896209 2481307239073488800172157)
        ·
          refine ⟨930490214652558300064559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2481307239073488800172157 930490214652558300064559)
          ·
            refine ⟨1395735321978837450096839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 930490214652558300064559 1395735321978837450096839)
            ·
              refine ⟨2093602982968256175145259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1395735321978837450096839 2093602982968256175145259)
              ·
                refine ⟨3140404474452384262717889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2093602982968256175145259 3140404474452384262717889)
                ·
                  refine ⟨2355303355839288197038417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3140404474452384262717889 2355303355839288197038417)
                  ·
                    refine ⟨1766477516879466147778813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2355303355839288197038417 1766477516879466147778813)
                    ·
                      refine ⟨662429068829799805417055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1766477516879466147778813 662429068829799805417055)
                      ·
                        rfl

theorem cell23_1290076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_1290076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290076 prefixEnd_1290076 := by exact prefixLift 1290076
  have htrace : WordTrace (prefixWord ++ tailWord_1290076) baseStart_1290076 baseEnd_1290076 := by
    simpa [prefixWord, tailWord_1290076, baseEnd_1290076] using wordTrace_append hprefix tailTrace_1290076
  have hstable : (prefixWord ++ tailWord_1290076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290076).length < 2 ^ (prefixWord ++ tailWord_1290076).sum := by decide
  have hdescent : baseEnd_1290076 < baseStart_1290076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290092 : List Nat := [2, 2, 1, 1, 4, 2, 4, 1, 1, 5]
def baseStart_1290092 : Nat := 118140960795 + 1290092 * 2 ^ 59
def prefixEnd_1290092 : Nat := 4983230072969 + 3 ^ 40 * 1290092 * 2
def baseEnd_1290092 : Nat := 220812428173423914272327

theorem tailTrace_1290092 : CollatzResearch.WordTrace tailWord_1290092 prefixEnd_1290092 220812428173423914272327 := by
  unfold tailWord_1290092
  simp only [CollatzResearch.WordTrace]
  refine ⟨23526760421112244508664265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31369013894816326011552353 23526760421112244508664265)
  ·
    refine ⟨17645070315834183381498199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23526760421112244508664265 17645070315834183381498199)
    ·
      refine ⟨26467605473751275072247299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17645070315834183381498199 26467605473751275072247299)
      ·
        refine ⟨39701408210626912608370949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26467605473751275072247299 39701408210626912608370949)
        ·
          refine ⟨7444014039492546114069553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39701408210626912608370949 7444014039492546114069553)
          ·
            refine ⟨5583010529619409585552165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7444014039492546114069553 5583010529619409585552165)
            ·
              refine ⟨1046814474303639297291031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5583010529619409585552165 1046814474303639297291031)
              ·
                refine ⟨1570221711455458945936547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1046814474303639297291031 1570221711455458945936547)
                ·
                  refine ⟨2355332567183188418904821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1570221711455458945936547 2355332567183188418904821)
                  ·
                    refine ⟨220812428173423914272327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2355332567183188418904821 220812428173423914272327)
                    ·
                      rfl

theorem cell23_1290092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 5].length) (baseStart_1290092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290092 prefixEnd_1290092 := by exact prefixLift 1290092
  have htrace : WordTrace (prefixWord ++ tailWord_1290092) baseStart_1290092 baseEnd_1290092 := by
    simpa [prefixWord, tailWord_1290092, baseEnd_1290092] using wordTrace_append hprefix tailTrace_1290092
  have hstable : (prefixWord ++ tailWord_1290092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290092).length < 2 ^ (prefixWord ++ tailWord_1290092).sum := by decide
  have hdescent : baseEnd_1290092 < baseStart_1290092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290105 : List Nat := [1, 2, 1, 3, 2, 2, 3, 1, 4, 4]
def baseStart_1290105 : Nat := 118140960795 + 1290105 * 2 ^ 59
def prefixEnd_1290105 : Nat := 4983230072969 + 3 ^ 40 * 1290105 * 2
def baseEnd_1290105 : Nat := 220814653256260063984807

theorem tailTrace_1290105 : CollatzResearch.WordTrace tailWord_1290105 prefixEnd_1290105 220814653256260063984807 := by
  unfold tailWord_1290105
  simp only [CollatzResearch.WordTrace]
  refine ⟨47053994991177392237551769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31369329994118261491701179 47053994991177392237551769)
  ·
    refine ⟨35290496243383044178163827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47053994991177392237551769 35290496243383044178163827)
    ·
      refine ⟨52935744365074566267245741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35290496243383044178163827 52935744365074566267245741)
      ·
        refine ⟨19850904136902962350217153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52935744365074566267245741 19850904136902962350217153)
        ·
          refine ⟨14888178102677221762662865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19850904136902962350217153 14888178102677221762662865)
          ·
            refine ⟨11166133577007916321997149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14888178102677221762662865 11166133577007916321997149)
            ·
              refine ⟨4187300091377968620748931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11166133577007916321997149 4187300091377968620748931)
              ·
                refine ⟨6280950137066952931123397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4187300091377968620748931 6280950137066952931123397)
                ·
                  refine ⟨1177678150700053674585637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6280950137066952931123397 1177678150700053674585637)
                  ·
                    refine ⟨220814653256260063984807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1177678150700053674585637 220814653256260063984807)
                    ·
                      rfl

theorem cell23_1290105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4, 4].length) (baseStart_1290105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290105 prefixEnd_1290105 := by exact prefixLift 1290105
  have htrace : WordTrace (prefixWord ++ tailWord_1290105) baseStart_1290105 baseEnd_1290105 := by
    simpa [prefixWord, tailWord_1290105, baseEnd_1290105] using wordTrace_append hprefix tailTrace_1290105
  have hstable : (prefixWord ++ tailWord_1290105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290105).length < 2 ^ (prefixWord ++ tailWord_1290105).sum := by decide
  have hdescent : baseEnd_1290105 < baseStart_1290105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290108 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 2, 6, 4]
def baseStart_1290108 : Nat := 118140960795 + 1290108 * 2 ^ 59
def prefixEnd_1290108 : Nat := 4983230072969 + 3 ^ 40 * 1290108 * 2
def baseEnd_1290108 : Nat := 662445500210743680216907

theorem tailTrace_1290108 : CollatzResearch.WordTrace tailWord_1290108 prefixEnd_1290108 662445500210743680216907 := by
  unfold tailWord_1290108
  simp only [CollatzResearch.WordTrace]
  refine ⟨23527052205083261874955489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31369402940111015833273985 23527052205083261874955489)
  ·
    refine ⟨17645289153812446406216617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23527052205083261874955489 17645289153812446406216617)
    ·
      refine ⟨13233966865359334804662463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17645289153812446406216617 13233966865359334804662463)
      ·
        refine ⟨19850950298039002206993695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13233966865359334804662463 19850950298039002206993695)
        ·
          refine ⟨29776425447058503310490543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19850950298039002206993695 29776425447058503310490543)
          ·
            refine ⟨44664638170587754965735815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29776425447058503310490543 44664638170587754965735815)
            ·
              refine ⟨66996957255881632448603723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44664638170587754965735815 66996957255881632448603723)
              ·
                refine ⟨100495435883822448672905585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66996957255881632448603723 100495435883822448672905585)
                ·
                  refine ⟨75371576912866836504679189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100495435883822448672905585 75371576912866836504679189)
                  ·
                    refine ⟨3533042667790632961156837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 75371576912866836504679189 3533042667790632961156837)
                    ·
                      refine ⟨662445500210743680216907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3533042667790632961156837 662445500210743680216907)
                      ·
                        rfl

theorem cell23_1290108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_1290108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290108 prefixEnd_1290108 := by exact prefixLift 1290108
  have htrace : WordTrace (prefixWord ++ tailWord_1290108) baseStart_1290108 baseEnd_1290108 := by
    simpa [prefixWord, tailWord_1290108, baseEnd_1290108] using wordTrace_append hprefix tailTrace_1290108
  have hstable : (prefixWord ++ tailWord_1290108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290108).length < 2 ^ (prefixWord ++ tailWord_1290108).sum := by decide
  have hdescent : baseEnd_1290108 < baseStart_1290108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290115 : List Nat := [1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 5]
def baseStart_1290115 : Nat := 118140960795 + 1290115 * 2 ^ 59
def prefixEnd_1290115 : Nat := 4983230072969 + 3 ^ 40 * 1290115 * 2
def baseEnd_1290115 : Nat := 662449094575325152829375

theorem tailTrace_1290115 : CollatzResearch.WordTrace tailWord_1290115 prefixEnd_1290115 662449094575325152829375 := by
  unfold tailWord_1290115
  simp only [CollatzResearch.WordTrace]
  refine ⟨47054359721141163945415799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31369573147427442630277199 47054359721141163945415799)
  ·
    refine ⟨70581539581711745918123699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47054359721141163945415799 70581539581711745918123699)
    ·
      refine ⟨105872309372567618877185549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70581539581711745918123699 105872309372567618877185549)
      ·
        refine ⟨39702116014712857078944581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105872309372567618877185549 39702116014712857078944581)
        ·
          refine ⟨7444146752758660702302109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39702116014712857078944581 7444146752758660702302109)
          ·
            refine ⟨2791555032284497763363291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7444146752758660702302109 2791555032284497763363291)
            ·
              refine ⟨4187332548426746645044937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2791555032284497763363291 4187332548426746645044937)
              ·
                refine ⟨3140499411320059983783703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4187332548426746645044937 3140499411320059983783703)
                ·
                  refine ⟨4710749116980089975675555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3140499411320059983783703 4710749116980089975675555)
                  ·
                    refine ⟨7066123675470134963513333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4710749116980089975675555 7066123675470134963513333)
                    ·
                      refine ⟨662449094575325152829375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7066123675470134963513333 662449094575325152829375)
                      ·
                        rfl

theorem cell23_1290115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_1290115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290115 prefixEnd_1290115 := by exact prefixLift 1290115
  have htrace : WordTrace (prefixWord ++ tailWord_1290115) baseStart_1290115 baseEnd_1290115 := by
    simpa [prefixWord, tailWord_1290115, baseEnd_1290115] using wordTrace_append hprefix tailTrace_1290115
  have hstable : (prefixWord ++ tailWord_1290115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290115).length < 2 ^ (prefixWord ++ tailWord_1290115).sum := by decide
  have hdescent : baseEnd_1290115 < baseStart_1290115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290135 : List Nat := [1, 1, 3, 3, 1, 3, 4, 7]
def baseStart_1290135 : Nat := 118140960795 + 1290135 * 2 ^ 59
def prefixEnd_1290135 : Nat := 4983230072969 + 3 ^ 40 * 1290135 * 2
def baseEnd_1290135 : Nat := 24535532006978336095529

theorem tailTrace_1290135 : CollatzResearch.WordTrace tailWord_1290135 prefixEnd_1290135 24535532006978336095529 := by
  unfold tailWord_1290135
  simp only [CollatzResearch.WordTrace]
  refine ⟨47055089181068707361143859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31370059454045804907429239 47055089181068707361143859)
  ·
    refine ⟨70582633771603061041715789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47055089181068707361143859 70582633771603061041715789)
    ·
      refine ⟨26468487664351147890643421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70582633771603061041715789 26468487664351147890643421)
      ·
        refine ⟨9925682874131680458991283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26468487664351147890643421 9925682874131680458991283)
        ·
          refine ⟨14888524311197520688486925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9925682874131680458991283 14888524311197520688486925)
          ·
            refine ⟨5583196616699070258182597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14888524311197520688486925 5583196616699070258182597)
            ·
              refine ⟨1046849365631075673409237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5583196616699070258182597 1046849365631075673409237)
              ·
                refine ⟨24535532006978336095529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1046849365631075673409237 24535532006978336095529)
                ·
                  rfl

theorem cell23_1290135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 7].length) (baseStart_1290135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290135 prefixEnd_1290135 := by exact prefixLift 1290135
  have htrace : WordTrace (prefixWord ++ tailWord_1290135) baseStart_1290135 baseEnd_1290135 := by
    simpa [prefixWord, tailWord_1290135, baseEnd_1290135] using wordTrace_append hprefix tailTrace_1290135
  have hstable : (prefixWord ++ tailWord_1290135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290135).length < 2 ^ (prefixWord ++ tailWord_1290135).sum := by decide
  have hdescent : baseEnd_1290135 < baseStart_1290135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290222 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 2, 4, 3]
def baseStart_1290222 : Nat := 118140960795 + 1290222 * 2 ^ 59
def prefixEnd_1290222 : Nat := 4983230072969 + 3 ^ 40 * 1290222 * 2
def baseEnd_1290222 : Nat := 662504037005356234191383

theorem tailTrace_1290222 : CollatzResearch.WordTrace tailWord_1290222 prefixEnd_1290222 662504037005356234191383 := by
  unfold tailWord_1290222
  simp only [CollatzResearch.WordTrace]
  refine ⟨5882282791469190152445115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31372174887835680813040613 5882282791469190152445115)
  ·
    refine ⟨8823424187203785228667673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5882282791469190152445115 8823424187203785228667673)
    ·
      refine ⟨6617568140402838921500755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8823424187203785228667673 6617568140402838921500755)
      ·
        refine ⟨9926352210604258382251133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6617568140402838921500755 9926352210604258382251133)
        ·
          refine ⟨3722382078976596893344175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9926352210604258382251133 3722382078976596893344175)
          ·
            refine ⟨5583573118464895340016263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3722382078976596893344175 5583573118464895340016263)
            ·
              refine ⟨8375359677697343010024395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5583573118464895340016263 8375359677697343010024395)
              ·
                refine ⟨12563039516546014515036593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8375359677697343010024395 12563039516546014515036593)
                ·
                  refine ⟨9422279637409510886277445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12563039516546014515036593 9422279637409510886277445)
                  ·
                    refine ⟨1766677432014283291177021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9422279637409510886277445 1766677432014283291177021)
                    ·
                      refine ⟨662504037005356234191383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1766677432014283291177021 662504037005356234191383)
                      ·
                        rfl

theorem cell23_1290222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_1290222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290222 prefixEnd_1290222 := by exact prefixLift 1290222
  have htrace : WordTrace (prefixWord ++ tailWord_1290222) baseStart_1290222 baseEnd_1290222 := by
    simpa [prefixWord, tailWord_1290222, baseEnd_1290222] using wordTrace_append hprefix tailTrace_1290222
  have hstable : (prefixWord ++ tailWord_1290222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290222).length < 2 ^ (prefixWord ++ tailWord_1290222).sum := by decide
  have hdescent : baseEnd_1290222 < baseStart_1290222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290235 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 1, 5, 3]
def baseStart_1290235 : Nat := 118140960795 + 1290235 * 2 ^ 59
def prefixEnd_1290235 : Nat := 4983230072969 + 3 ^ 40 * 1290235 * 2
def baseEnd_1290235 : Nat := 662510712253864683328823

theorem tailTrace_1290235 : CollatzResearch.WordTrace tailWord_1290235 prefixEnd_1290235 662510712253864683328823 := by
  unfold tailWord_1290235
  simp only [CollatzResearch.WordTrace]
  refine ⟨47058736480706424439784159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31372490987137616293189439 47058736480706424439784159)
  ·
    refine ⟨70588104721059636659676239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47058736480706424439784159 70588104721059636659676239)
    ·
      refine ⟨105882157081589454989514359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70588104721059636659676239 105882157081589454989514359)
      ·
        refine ⟨158823235622384182484271539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105882157081589454989514359 158823235622384182484271539)
        ·
          refine ⟨238234853433576273726407309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158823235622384182484271539 238234853433576273726407309)
          ·
            refine ⟨89338070037591102647402741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 238234853433576273726407309 89338070037591102647402741)
            ·
              refine ⟨8375444066024165873194007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89338070037591102647402741 8375444066024165873194007)
              ·
                refine ⟨12563166099036248809791011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8375444066024165873194007 12563166099036248809791011)
                ·
                  refine ⟨18844749148554373214686517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12563166099036248809791011 18844749148554373214686517)
                  ·
                    refine ⟨1766695232676972488876861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18844749148554373214686517 1766695232676972488876861)
                    ·
                      refine ⟨662510712253864683328823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1766695232676972488876861 662510712253864683328823)
                      ·
                        rfl

theorem cell23_1290235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5, 3].length) (baseStart_1290235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290235 prefixEnd_1290235 := by exact prefixLift 1290235
  have htrace : WordTrace (prefixWord ++ tailWord_1290235) baseStart_1290235 baseEnd_1290235 := by
    simpa [prefixWord, tailWord_1290235, baseEnd_1290235] using wordTrace_append hprefix tailTrace_1290235
  have hstable : (prefixWord ++ tailWord_1290235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290235).length < 2 ^ (prefixWord ++ tailWord_1290235).sum := by decide
  have hdescent : baseEnd_1290235 < baseStart_1290235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290326 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_1290326 : Nat := 118140960795 + 1290326 * 2 ^ 59
def prefixEnd_1290326 : Nat := 4983230072969 + 3 ^ 40 * 1290326 * 2
def baseEnd_1290326 : Nat := 662557438993423827290905

theorem tailTrace_1290326 : CollatzResearch.WordTrace tailWord_1290326 prefixEnd_1290326 662557438993423827290905 := by
  unfold tailWord_1290326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2941378470211046686334177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31374703682251164654231221 2941378470211046686334177)
  ·
    refine ⟨2206033852658285014750633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2941378470211046686334177 2206033852658285014750633)
    ·
      refine ⟨1654525389493713761062975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2206033852658285014750633 1654525389493713761062975)
      ·
        refine ⟨2481788084240570641594463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1654525389493713761062975 2481788084240570641594463)
        ·
          refine ⟨3722682126360855962391695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2481788084240570641594463 3722682126360855962391695)
          ·
            refine ⟨5584023189541283943587543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3722682126360855962391695 5584023189541283943587543)
            ·
              refine ⟨8376034784311925915381315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5584023189541283943587543 8376034784311925915381315)
              ·
                refine ⟨12564052176467888873071973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8376034784311925915381315 12564052176467888873071973)
                ·
                  refine ⟨2355759783087729163700995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12564052176467888873071973 2355759783087729163700995)
                  ·
                    refine ⟨3533639674631593745551493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2355759783087729163700995 3533639674631593745551493)
                    ·
                      refine ⟨662557438993423827290905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3533639674631593745551493 662557438993423827290905)
                      ·
                        rfl

theorem cell23_1290326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_1290326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290326 prefixEnd_1290326 := by exact prefixLift 1290326
  have htrace : WordTrace (prefixWord ++ tailWord_1290326) baseStart_1290326 baseEnd_1290326 := by
    simpa [prefixWord, tailWord_1290326, baseEnd_1290326] using wordTrace_append hprefix tailTrace_1290326
  have hstable : (prefixWord ++ tailWord_1290326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290326).length < 2 ^ (prefixWord ++ tailWord_1290326).sum := by decide
  have hdescent : baseEnd_1290326 < baseStart_1290326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290332 : List Nat := [2, 2, 4, 1, 1, 2, 2, 1, 8]
def baseStart_1290332 : Nat := 118140960795 + 1290332 * 2 ^ 59
def prefixEnd_1290332 : Nat := 4983230072969 + 3 ^ 40 * 1290332 * 2
def baseEnd_1290332 : Nat := 73617835541927867090653

theorem tailTrace_1290332 : CollatzResearch.WordTrace tailWord_1290332 prefixEnd_1290332 73617835541927867090653 := by
  unfold tailWord_1290332
  simp only [CollatzResearch.WordTrace]
  refine ⟨23531137180677505003032625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31374849574236673337376833 23531137180677505003032625)
  ·
    refine ⟨17648352885508128752274469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23531137180677505003032625 17648352885508128752274469)
    ·
      refine ⟨3309066166032774141051463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17648352885508128752274469 3309066166032774141051463)
      ·
        refine ⟨4963599249049161211577195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3309066166032774141051463 4963599249049161211577195)
        ·
          refine ⟨7445398873573741817365793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4963599249049161211577195 7445398873573741817365793)
          ·
            refine ⟨5584049155180306363024345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7445398873573741817365793 5584049155180306363024345)
            ·
              refine ⟨4188036866385229772268259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5584049155180306363024345 4188036866385229772268259)
              ·
                refine ⟨6282055299577844658402389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4188036866385229772268259 6282055299577844658402389)
                ·
                  refine ⟨73617835541927867090653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6282055299577844658402389 73617835541927867090653)
                  ·
                    rfl

theorem cell23_1290332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 8].length) (baseStart_1290332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290332 prefixEnd_1290332 := by exact prefixLift 1290332
  have htrace : WordTrace (prefixWord ++ tailWord_1290332) baseStart_1290332 baseEnd_1290332 := by
    simpa [prefixWord, tailWord_1290332, baseEnd_1290332] using wordTrace_append hprefix tailTrace_1290332
  have hstable : (prefixWord ++ tailWord_1290332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290332).length < 2 ^ (prefixWord ++ tailWord_1290332).sum := by decide
  have hdescent : baseEnd_1290332 < baseStart_1290332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290335 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 6]
def baseStart_1290335 : Nat := 118140960795 + 1290335 * 2 ^ 59
def prefixEnd_1290335 : Nat := 4983230072969 + 3 ^ 40 * 1290335 * 2
def baseEnd_1290335 : Nat := 662562060319314292078363

theorem tailTrace_1290335 : CollatzResearch.WordTrace tailWord_1290335 prefixEnd_1290335 662562060319314292078363 := by
  unfold tailWord_1290335
  simp only [CollatzResearch.WordTrace]
  refine ⟨47062383780344141518424459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31374922520229427678949639 47062383780344141518424459)
  ·
    refine ⟨70593575670516212277636689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47062383780344141518424459 70593575670516212277636689)
    ·
      refine ⟨52945181752887159208227517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70593575670516212277636689 52945181752887159208227517)
      ·
        refine ⟨19854443157332684703085319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52945181752887159208227517 19854443157332684703085319)
        ·
          refine ⟨29781664735999027054627979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19854443157332684703085319 29781664735999027054627979)
          ·
            refine ⟨44672497103998540581941969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29781664735999027054627979 44672497103998540581941969)
            ·
              refine ⟨33504372827998905436456477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44672497103998540581941969 33504372827998905436456477)
              ·
                refine ⟨12564139810499589538671179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33504372827998905436456477 12564139810499589538671179)
                ·
                  refine ⟨18846209715749384308006769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12564139810499589538671179 18846209715749384308006769)
                  ·
                    refine ⟨14134657286812038231005077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18846209715749384308006769 14134657286812038231005077)
                    ·
                      refine ⟨662562060319314292078363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14134657286812038231005077 662562060319314292078363)
                      ·
                        rfl

theorem cell23_1290335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_1290335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290335 prefixEnd_1290335 := by exact prefixLift 1290335
  have htrace : WordTrace (prefixWord ++ tailWord_1290335) baseStart_1290335 baseEnd_1290335 := by
    simpa [prefixWord, tailWord_1290335, baseEnd_1290335] using wordTrace_append hprefix tailTrace_1290335
  have hstable : (prefixWord ++ tailWord_1290335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290335).length < 2 ^ (prefixWord ++ tailWord_1290335).sum := by decide
  have hdescent : baseEnd_1290335 < baseStart_1290335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290386 : List Nat := [3, 2, 3, 1, 1, 1, 1, 4, 2, 3, 2]
def baseStart_1290386 : Nat := 118140960795 + 1290386 * 2 ^ 59
def prefixEnd_1290386 : Nat := 4983230072969 + 3 ^ 40 * 1290386 * 2
def baseEnd_1290386 : Nat := 662588247832693592540629

theorem tailTrace_1290386 : CollatzResearch.WordTrace tailWord_1290386 prefixEnd_1290386 662588247832693592540629 := by
  unfold tailWord_1290386
  simp only [CollatzResearch.WordTrace]
  refine ⟨11766060975789844307132753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31376162602106251485687341 11766060975789844307132753)
  ·
    refine ⟨8824545731842383230349565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11766060975789844307132753 8824545731842383230349565)
    ·
      refine ⟨3309204649440893711381087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8824545731842383230349565 3309204649440893711381087)
      ·
        refine ⟨4963806974161340567071631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3309204649440893711381087 4963806974161340567071631)
        ·
          refine ⟨7445710461242010850607447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4963806974161340567071631 7445710461242010850607447)
          ·
            refine ⟨11168565691863016275911171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7445710461242010850607447 11168565691863016275911171)
            ·
              refine ⟨16752848537794524413866757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11168565691863016275911171 16752848537794524413866757)
              ·
                refine ⟨3141159100836473327600017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16752848537794524413866757 3141159100836473327600017)
                ·
                  refine ⟨2355869325627354995700013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3141159100836473327600017 2355869325627354995700013)
                  ·
                    refine ⟨883450997110258123387505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2355869325627354995700013 883450997110258123387505)
                    ·
                      refine ⟨662588247832693592540629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 883450997110258123387505 662588247832693592540629)
                      ·
                        rfl

theorem cell23_1290386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_1290386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290386 prefixEnd_1290386 := by exact prefixLift 1290386
  have htrace : WordTrace (prefixWord ++ tailWord_1290386) baseStart_1290386 baseEnd_1290386 := by
    simpa [prefixWord, tailWord_1290386, baseEnd_1290386] using wordTrace_append hprefix tailTrace_1290386
  have hstable : (prefixWord ++ tailWord_1290386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290386).length < 2 ^ (prefixWord ++ tailWord_1290386).sum := by decide
  have hdescent : baseEnd_1290386 < baseStart_1290386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290399 : List Nat := [1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 4]
def baseStart_1290399 : Nat := 118140960795 + 1290399 * 2 ^ 59
def prefixEnd_1290399 : Nat := 4983230072969 + 3 ^ 40 * 1290399 * 2
def baseEnd_1290399 : Nat := 662594923081202041678069

theorem tailTrace_1290399 : CollatzResearch.WordTrace tailWord_1290399 prefixEnd_1290399 662594923081202041678069 := by
  unfold tailWord_1290399
  simp only [CollatzResearch.WordTrace]
  refine ⟨47064718052112280448754251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31376478701408186965836167 47064718052112280448754251)
  ·
    refine ⟨70597077078168420673131377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47064718052112280448754251 70597077078168420673131377)
    ·
      refine ⟨52947807808626315504848533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70597077078168420673131377 52947807808626315504848533)
      ·
        refine ⟨2481928491029358539289775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 52947807808626315504848533 2481928491029358539289775)
        ·
          refine ⟨3722892736544037808934663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2481928491029358539289775 3722892736544037808934663)
          ·
            refine ⟨5584339104816056713401995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3722892736544037808934663 5584339104816056713401995)
            ·
              refine ⟨8376508657224085070102993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5584339104816056713401995 8376508657224085070102993)
              ·
                refine ⟨6282381492918063802577245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8376508657224085070102993 6282381492918063802577245)
                ·
                  refine ⟨2355893059844273925966467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6282381492918063802577245 2355893059844273925966467)
                  ·
                    refine ⟨3533839589766410888949701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2355893059844273925966467 3533839589766410888949701)
                    ·
                      refine ⟨662594923081202041678069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3533839589766410888949701 662594923081202041678069)
                      ·
                        rfl

theorem cell23_1290399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_1290399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290399 prefixEnd_1290399 := by exact prefixLift 1290399
  have htrace : WordTrace (prefixWord ++ tailWord_1290399) baseStart_1290399 baseEnd_1290399 := by
    simpa [prefixWord, tailWord_1290399, baseEnd_1290399] using wordTrace_append hprefix tailTrace_1290399
  have hstable : (prefixWord ++ tailWord_1290399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290399).length < 2 ^ (prefixWord ++ tailWord_1290399).sum := by decide
  have hdescent : baseEnd_1290399 < baseStart_1290399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290419 : List Nat := [1, 1, 1, 2, 3, 2, 1, 6, 1, 2, 3]
def baseStart_1290419 : Nat := 118140960795 + 1290419 * 2 ^ 59
def prefixEnd_1290419 : Nat := 4983230072969 + 3 ^ 40 * 1290419 * 2
def baseEnd_1290419 : Nat := 662605192694291963427977

theorem tailTrace_1290419 : CollatzResearch.WordTrace tailWord_1290419 prefixEnd_1290419 662605192694291963427977 := by
  unfold tailWord_1290419
  simp only [CollatzResearch.WordTrace]
  refine ⟨47065447512039823864482311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31376965008026549242988207 47065447512039823864482311)
  ·
    refine ⟨70598171268059735796723467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47065447512039823864482311 70598171268059735796723467)
    ·
      refine ⟨105897256902089603695085201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70598171268059735796723467 105897256902089603695085201)
      ·
        refine ⟨79422942676567202771313901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105897256902089603695085201 79422942676567202771313901)
        ·
          refine ⟨29783603503712701039242713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79422942676567202771313901 29783603503712701039242713)
          ·
            refine ⟨22337702627784525779432035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29783603503712701039242713 22337702627784525779432035)
            ·
              refine ⟨33506553941676788669148053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22337702627784525779432035 33506553941676788669148053)
              ·
                refine ⟨1570619716016099468866315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33506553941676788669148053 1570619716016099468866315)
                ·
                  refine ⟨2355929574024149203299473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1570619716016099468866315 2355929574024149203299473)
                  ·
                    refine ⟨1766947180518111902474605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2355929574024149203299473 1766947180518111902474605)
                    ·
                      refine ⟨662605192694291963427977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1766947180518111902474605 662605192694291963427977)
                      ·
                        rfl

theorem cell23_1290419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 2, 3].length) (baseStart_1290419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290419 prefixEnd_1290419 := by exact prefixLift 1290419
  have htrace : WordTrace (prefixWord ++ tailWord_1290419) baseStart_1290419 baseEnd_1290419 := by
    simpa [prefixWord, tailWord_1290419, baseEnd_1290419] using wordTrace_append hprefix tailTrace_1290419
  have hstable : (prefixWord ++ tailWord_1290419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290419).length < 2 ^ (prefixWord ++ tailWord_1290419).sum := by decide
  have hdescent : baseEnd_1290419 < baseStart_1290419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290430 : List Nat := [4, 2, 1, 1, 5, 1, 2, 1, 1, 5]
def baseStart_1290430 : Nat := 118140960795 + 1290430 * 2 ^ 59
def prefixEnd_1290430 : Nat := 4983230072969 + 3 ^ 40 * 1290430 * 2
def baseEnd_1290430 : Nat := 220870280327163806796809

theorem tailTrace_1290430 : CollatzResearch.WordTrace tailWord_1290430 prefixEnd_1290430 220870280327163806796809 := by
  unfold tailWord_1290430
  simp only [CollatzResearch.WordTrace]
  refine ⟨5883231089374996592891593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31377232476666648495421829 5883231089374996592891593)
  ·
    refine ⟨4412423317031247444668695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5883231089374996592891593 4412423317031247444668695)
    ·
      refine ⟨6618634975546871167003043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4412423317031247444668695 6618634975546871167003043)
      ·
        refine ⟨9927952463320306750504565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6618634975546871167003043 9927952463320306750504565)
        ·
          refine ⟨930745543436278757859803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9927952463320306750504565 930745543436278757859803)
          ·
            refine ⟨1396118315154418136789705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 930745543436278757859803 1396118315154418136789705)
            ·
              refine ⟨1047088736365813602592279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1396118315154418136789705 1047088736365813602592279)
              ·
                refine ⟨1570633104548720403888419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1047088736365813602592279 1570633104548720403888419)
                ·
                  refine ⟨2355949656823080605832629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1570633104548720403888419 2355949656823080605832629)
                  ·
                    refine ⟨220870280327163806796809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2355949656823080605832629 220870280327163806796809)
                    ·
                      rfl

theorem cell23_1290430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_1290430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290430 prefixEnd_1290430 := by exact prefixLift 1290430
  have htrace : WordTrace (prefixWord ++ tailWord_1290430) baseStart_1290430 baseEnd_1290430 := by
    simpa [prefixWord, tailWord_1290430, baseEnd_1290430] using wordTrace_append hprefix tailTrace_1290430
  have hstable : (prefixWord ++ tailWord_1290430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290430).length < 2 ^ (prefixWord ++ tailWord_1290430).sum := by decide
  have hdescent : baseEnd_1290430 < baseStart_1290430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290433 : List Nat := [1, 2, 6, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_1290433 : Nat := 118140960795 + 1290433 * 2 ^ 59
def prefixEnd_1290433 : Nat := 4983230072969 + 3 ^ 40 * 1290433 * 2
def baseEnd_1290433 : Nat := 662612381423454908652913

theorem tailTrace_1290433 : CollatzResearch.WordTrace tailWord_1290433 prefixEnd_1290433 662612381423454908652913 := by
  unfold tailWord_1290433
  simp only [CollatzResearch.WordTrace]
  refine ⟨47065958133989104255491953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31377305422659402836994635 47065958133989104255491953)
  ·
    refine ⟨35299468600491828191618965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47065958133989104255491953 35299468600491828191618965)
    ·
      refine ⟨1654662590648054446482139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 35299468600491828191618965 1654662590648054446482139)
      ·
        refine ⟨2481993885972081669723209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1654662590648054446482139 2481993885972081669723209)
        ·
          refine ⟨1861495414479061252292407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2481993885972081669723209 1861495414479061252292407)
          ·
            refine ⟨2792243121718591878438611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1861495414479061252292407 2792243121718591878438611)
            ·
              refine ⟨4188364682577887817657917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2792243121718591878438611 4188364682577887817657917)
              ·
                refine ⟨1570636755966707931621719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4188364682577887817657917 1570636755966707931621719)
                ·
                  refine ⟨2355955133950061897432579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1570636755966707931621719 2355955133950061897432579)
                  ·
                    refine ⟨3533932700925092846148869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2355955133950061897432579 3533932700925092846148869)
                    ·
                      refine ⟨662612381423454908652913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3533932700925092846148869 662612381423454908652913)
                      ·
                        rfl

theorem cell23_1290433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_1290433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290433 prefixEnd_1290433 := by exact prefixLift 1290433
  have htrace : WordTrace (prefixWord ++ tailWord_1290433) baseStart_1290433 baseEnd_1290433 := by
    simpa [prefixWord, tailWord_1290433, baseEnd_1290433] using wordTrace_append hprefix tailTrace_1290433
  have hstable : (prefixWord ++ tailWord_1290433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290433).length < 2 ^ (prefixWord ++ tailWord_1290433).sum := by decide
  have hdescent : baseEnd_1290433 < baseStart_1290433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290450 : List Nat := [3, 2, 2, 2, 1, 2, 2, 4, 1, 2, 2]
def baseStart_1290450 : Nat := 118140960795 + 1290450 * 2 ^ 59
def prefixEnd_1290450 : Nat := 4983230072969 + 3 ^ 40 * 1290450 * 2
def baseEnd_1290450 : Nat := 662621110594581342140335

theorem tailTrace_1290450 : CollatzResearch.WordTrace tailWord_1290450 prefixEnd_1290450 662621110594581342140335 := by
  unfold tailWord_1290450
  simp only [CollatzResearch.WordTrace]
  refine ⟨11766644543731879039715201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31377718783285010772573869 11766644543731879039715201)
  ·
    refine ⟨8824983407798909279786401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11766644543731879039715201 8824983407798909279786401)
    ·
      refine ⟨6618737555849181959839801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8824983407798909279786401 6618737555849181959839801)
      ·
        refine ⟨4964053166886886469879851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6618737555849181959839801 4964053166886886469879851)
        ·
          refine ⟨7446079750330329704819777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4964053166886886469879851 7446079750330329704819777)
          ·
            refine ⟨5584559812747747278614833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7446079750330329704819777 5584559812747747278614833)
            ·
              refine ⟨4188419859560810458961125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5584559812747747278614833 4188419859560810458961125)
              ·
                refine ⟨785328723667651961055211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4188419859560810458961125 785328723667651961055211)
                ·
                  refine ⟨1177993085501477941582817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 785328723667651961055211 1177993085501477941582817)
                  ·
                    refine ⟨883494814126108456187113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1177993085501477941582817 883494814126108456187113)
                    ·
                      refine ⟨662621110594581342140335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 883494814126108456187113 662621110594581342140335)
                      ·
                        rfl

theorem cell23_1290450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_1290450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290450 prefixEnd_1290450 := by exact prefixLift 1290450
  have htrace : WordTrace (prefixWord ++ tailWord_1290450) baseStart_1290450 baseEnd_1290450 := by
    simpa [prefixWord, tailWord_1290450, baseEnd_1290450] using wordTrace_append hprefix tailTrace_1290450
  have hstable : (prefixWord ++ tailWord_1290450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290450).length < 2 ^ (prefixWord ++ tailWord_1290450).sum := by decide
  have hdescent : baseEnd_1290450 < baseStart_1290450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290460 : List Nat := [2, 2, 5, 2, 2, 1, 1, 1, 1, 6]
def baseStart_1290460 : Nat := 118140960795 + 1290460 * 2 ^ 59
def prefixEnd_1290460 : Nat := 4983230072969 + 3 ^ 40 * 1290460 * 2
def baseEnd_1290460 : Nat := 220875415133708767671763

theorem tailTrace_1290460 : CollatzResearch.WordTrace tailWord_1290460 prefixEnd_1290460 220875415133708767671763 := by
  unfold tailWord_1290460
  simp only [CollatzResearch.WordTrace]
  refine ⟨23533471452445643933362417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31377961936594191911149889 23533471452445643933362417)
  ·
    refine ⟨17650103589334232950021813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23533471452445643933362417 17650103589334232950021813)
    ·
      refine ⟨1654697211500084339064545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17650103589334232950021813 1654697211500084339064545)
      ·
        refine ⟨1241022908625063254298409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1654697211500084339064545 1241022908625063254298409)
        ·
          refine ⟨930767181468797440723807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1241022908625063254298409 930767181468797440723807)
          ·
            refine ⟨1396150772203196161085711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 930767181468797440723807 1396150772203196161085711)
            ·
              refine ⟨2094226158304794241628567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1396150772203196161085711 2094226158304794241628567)
              ·
                refine ⟨3141339237457191362442851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2094226158304794241628567 3141339237457191362442851)
                ·
                  refine ⟨4712008856185787043664277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3141339237457191362442851 4712008856185787043664277)
                  ·
                    refine ⟨220875415133708767671763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4712008856185787043664277 220875415133708767671763)
                    ·
                      rfl

theorem cell23_1290460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_1290460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290460 prefixEnd_1290460 := by exact prefixLift 1290460
  have htrace : WordTrace (prefixWord ++ tailWord_1290460) baseStart_1290460 baseEnd_1290460 := by
    simpa [prefixWord, tailWord_1290460, baseEnd_1290460] using wordTrace_append hprefix tailTrace_1290460
  have hstable : (prefixWord ++ tailWord_1290460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290460).length < 2 ^ (prefixWord ++ tailWord_1290460).sum := by decide
  have hdescent : baseEnd_1290460 < baseStart_1290460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290559 : List Nat := [1, 1, 2, 2, 4, 1, 1, 4, 2, 5]
def baseStart_1290559 : Nat := 118140960795 + 1290559 * 2 ^ 59
def prefixEnd_1290559 : Nat := 4983230072969 + 3 ^ 40 * 1290559 * 2
def baseEnd_1290559 : Nat := 220892359995307138559111

theorem tailTrace_1290559 : CollatzResearch.WordTrace tailWord_1290559 prefixEnd_1290559 220892359995307138559111 := by
  unfold tailWord_1290559
  simp only [CollatzResearch.WordTrace]
  refine ⟨47070553731532627774578731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31380369154355085183052487 47070553731532627774578731)
  ·
    refine ⟨70605830597298941661868097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47070553731532627774578731 70605830597298941661868097)
    ·
      refine ⟨52954372947974206246401073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70605830597298941661868097 52954372947974206246401073)
      ·
        refine ⟨39715779710980654684800805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52954372947974206246401073 39715779710980654684800805)
        ·
          refine ⟨7446708695808872753400151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39715779710980654684800805 7446708695808872753400151)
          ·
            refine ⟨11170063043713309130100227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7446708695808872753400151 11170063043713309130100227)
            ·
              refine ⟨16755094565569963695150341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11170063043713309130100227 16755094565569963695150341)
              ·
                refine ⟨3141580231044368192840689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16755094565569963695150341 3141580231044368192840689)
                ·
                  refine ⟨2356185173283276144630517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3141580231044368192840689 2356185173283276144630517)
                  ·
                    refine ⟨220892359995307138559111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2356185173283276144630517 220892359995307138559111)
                    ·
                      rfl

theorem cell23_1290559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 5].length) (baseStart_1290559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290559 prefixEnd_1290559 := by exact prefixLift 1290559
  have htrace : WordTrace (prefixWord ++ tailWord_1290559) baseStart_1290559 baseEnd_1290559 := by
    simpa [prefixWord, tailWord_1290559, baseEnd_1290559] using wordTrace_append hprefix tailTrace_1290559
  have hstable : (prefixWord ++ tailWord_1290559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290559).length < 2 ^ (prefixWord ++ tailWord_1290559).sum := by decide
  have hdescent : baseEnd_1290559 < baseStart_1290559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290596 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 1, 6, 2]
def baseStart_1290596 : Nat := 118140960795 + 1290596 * 2 ^ 59
def prefixEnd_1290596 : Nat := 4983230072969 + 3 ^ 40 * 1290596 * 2
def baseEnd_1290596 : Nat := 662696078770137770914663

theorem tailTrace_1290596 : CollatzResearch.WordTrace tailWord_1290596 prefixEnd_1290596 662696078770137770914663 := by
  unfold tailWord_1290596
  simp only [CollatzResearch.WordTrace]
  refine ⟨23535951616199291546837821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31381268821599055395783761 23535951616199291546837821)
  ·
    refine ⟨8825981856074734330064183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23535951616199291546837821 8825981856074734330064183)
    ·
      refine ⟨13238972784112101495096275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8825981856074734330064183 13238972784112101495096275)
      ·
        refine ⟨19858459176168152242644413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13238972784112101495096275 19858459176168152242644413)
        ·
          refine ⟨7446922191063057090991655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19858459176168152242644413 7446922191063057090991655)
          ·
            refine ⟨11170383286594585636487483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7446922191063057090991655 11170383286594585636487483)
            ·
              refine ⟨16755574929891878454731225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11170383286594585636487483 16755574929891878454731225)
              ·
                refine ⟨12566681197418908841048419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16755574929891878454731225 12566681197418908841048419)
                ·
                  refine ⟨18850021796128363261572629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12566681197418908841048419 18850021796128363261572629)
                  ·
                    refine ⟨883594771693517027886217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18850021796128363261572629 883594771693517027886217)
                    ·
                      refine ⟨662696078770137770914663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 883594771693517027886217 662696078770137770914663)
                      ·
                        rfl

theorem cell23_1290596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 1, 6, 2].length) (baseStart_1290596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290596 prefixEnd_1290596 := by exact prefixLift 1290596
  have htrace : WordTrace (prefixWord ++ tailWord_1290596) baseStart_1290596 baseEnd_1290596 := by
    simpa [prefixWord, tailWord_1290596, baseEnd_1290596] using wordTrace_append hprefix tailTrace_1290596
  have hstable : (prefixWord ++ tailWord_1290596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290596).length < 2 ^ (prefixWord ++ tailWord_1290596).sum := by decide
  have hdescent : baseEnd_1290596 < baseStart_1290596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290613 : List Nat := [1, 3, 4, 1, 2, 1, 1, 2, 2, 4, 2]
def baseStart_1290613 : Nat := 118140960795 + 1290613 * 2 ^ 59
def prefixEnd_1290613 : Nat := 4983230072969 + 3 ^ 40 * 1290613 * 2
def baseEnd_1290613 : Nat := 662704807941264204402085

theorem tailTrace_1290613 : CollatzResearch.WordTrace tailWord_1290613 prefixEnd_1290613 662704807941264204402085 := by
  unfold tailWord_1290613
  simp only [CollatzResearch.WordTrace]
  refine ⟨47072523273336994997044493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31381682182224663331362995 47072523273336994997044493)
  ·
    refine ⟨17652196227501373123891685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47072523273336994997044493 17652196227501373123891685)
    ·
      refine ⟨3309786792656507460729691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17652196227501373123891685 3309786792656507460729691)
      ·
        refine ⟨4964680188984761191094537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3309786792656507460729691 4964680188984761191094537)
        ·
          refine ⟨3723510141738570893320903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4964680188984761191094537 3723510141738570893320903)
          ·
            refine ⟨5585265212607856339981355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3723510141738570893320903 5585265212607856339981355)
            ·
              refine ⟨8377897818911784509972033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5585265212607856339981355 8377897818911784509972033)
              ·
                refine ⟨6283423364183838382479025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8377897818911784509972033 6283423364183838382479025)
                ·
                  refine ⟨4712567523137878786859269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6283423364183838382479025 4712567523137878786859269)
                  ·
                    refine ⟨883606410588352272536113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4712567523137878786859269 883606410588352272536113)
                    ·
                      refine ⟨662704807941264204402085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 883606410588352272536113 662704807941264204402085)
                      ·
                        rfl

theorem cell23_1290613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_1290613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290613 prefixEnd_1290613 := by exact prefixLift 1290613
  have htrace : WordTrace (prefixWord ++ tailWord_1290613) baseStart_1290613 baseEnd_1290613 := by
    simpa [prefixWord, tailWord_1290613, baseEnd_1290613] using wordTrace_append hprefix tailTrace_1290613
  have hstable : (prefixWord ++ tailWord_1290613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290613).length < 2 ^ (prefixWord ++ tailWord_1290613).sum := by decide
  have hdescent : baseEnd_1290613 < baseStart_1290613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290619 : List Nat := [1, 1, 1, 1, 1, 8, 1, 1, 8]
def baseStart_1290619 : Nat := 118140960795 + 1290619 * 2 ^ 59
def prefixEnd_1290619 : Nat := 4983230072969 + 3 ^ 40 * 1290619 * 2
def baseEnd_1290619 : Nat := 73634209869465686769673

theorem tailTrace_1290619 : CollatzResearch.WordTrace tailWord_1290619 prefixEnd_1290619 73634209869465686769673 := by
  unfold tailWord_1290619
  simp only [CollatzResearch.WordTrace]
  refine ⟨47072742111315258021762911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31381828074210172014508607 47072742111315258021762911)
  ·
    refine ⟨70609113166972887032644367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47072742111315258021762911 70609113166972887032644367)
    ·
      refine ⟨105913669750459330548966551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70609113166972887032644367 105913669750459330548966551)
      ·
        refine ⟨158870504625688995823449827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105913669750459330548966551 158870504625688995823449827)
        ·
          refine ⟨238305756938533493735174741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158870504625688995823449827 238305756938533493735174741)
          ·
            refine ⟨2792645589123439379709079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 238305756938533493735174741 2792645589123439379709079)
            ·
              refine ⟨4188968383685159069563619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2792645589123439379709079 4188968383685159069563619)
              ·
                refine ⟨6283452575527738604345429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4188968383685159069563619 6283452575527738604345429)
                ·
                  refine ⟨73634209869465686769673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6283452575527738604345429 73634209869465686769673)
                  ·
                    rfl

theorem cell23_1290619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 8].length) (baseStart_1290619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290619 prefixEnd_1290619 := by exact prefixLift 1290619
  have htrace : WordTrace (prefixWord ++ tailWord_1290619) baseStart_1290619 baseEnd_1290619 := by
    simpa [prefixWord, tailWord_1290619, baseEnd_1290619] using wordTrace_append hprefix tailTrace_1290619
  have hstable : (prefixWord ++ tailWord_1290619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290619).length < 2 ^ (prefixWord ++ tailWord_1290619).sum := by decide
  have hdescent : baseEnd_1290619 < baseStart_1290619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290673 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 4, 3, 2]
def baseStart_1290673 : Nat := 118140960795 + 1290673 * 2 ^ 59
def prefixEnd_1290673 : Nat := 4983230072969 + 3 ^ 40 * 1290673 * 2
def baseEnd_1290673 : Nat := 662735616780533969651809

theorem tailTrace_1290673 : CollatzResearch.WordTrace tailWord_1290673 prefixEnd_1290673 662735616780533969651809 := by
  unfold tailWord_1290673
  simp only [CollatzResearch.WordTrace]
  refine ⟨47074711653119625244228673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31383141102079750162819115 47074711653119625244228673)
  ·
    refine ⟨35306033739839718933171505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47074711653119625244228673 35306033739839718933171505)
    ·
      refine ⟨26479525304879789199878629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35306033739839718933171505 26479525304879789199878629)
      ·
        refine ⟨4964910994664960474977243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26479525304879789199878629 4964910994664960474977243)
        ·
          refine ⟨7447366491997440712465865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4964910994664960474977243 7447366491997440712465865)
          ·
            refine ⟨5585524868998080534349399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7447366491997440712465865 5585524868998080534349399)
            ·
              refine ⟨8378287303497120801524099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5585524868998080534349399 8378287303497120801524099)
              ·
                refine ⟨12567430955245681202286149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8378287303497120801524099 12567430955245681202286149)
                ·
                  refine ⟨2356393304108565225428653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12567430955245681202286149 2356393304108565225428653)
                  ·
                    refine ⟨883647489040711959535745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2356393304108565225428653 883647489040711959535745)
                    ·
                      refine ⟨662735616780533969651809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 883647489040711959535745 662735616780533969651809)
                      ·
                        rfl

theorem cell23_1290673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_1290673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290673 prefixEnd_1290673 := by exact prefixLift 1290673
  have htrace : WordTrace (prefixWord ++ tailWord_1290673) baseStart_1290673 baseEnd_1290673 := by
    simpa [prefixWord, tailWord_1290673, baseEnd_1290673] using wordTrace_append hprefix tailTrace_1290673
  have hstable : (prefixWord ++ tailWord_1290673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290673).length < 2 ^ (prefixWord ++ tailWord_1290673).sum := by decide
  have hdescent : baseEnd_1290673 < baseStart_1290673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290700 : List Nat := [2, 2, 1, 4, 3, 2, 1, 2, 1, 5]
def baseStart_1290700 : Nat := 118140960795 + 1290700 * 2 ^ 59
def prefixEnd_1290700 : Nat := 4983230072969 + 3 ^ 40 * 1290700 * 2
def baseEnd_1290700 : Nat := 220916493586068454671395

theorem tailTrace_1290700 : CollatzResearch.WordTrace tailWord_1290700 prefixEnd_1290700 220916493586068454671395 := by
  unfold tailWord_1290700
  simp only [CollatzResearch.WordTrace]
  refine ⟨23537848212010904427730777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31383797616014539236974369 23537848212010904427730777)
  ·
    refine ⟨17653386159008178320798083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23537848212010904427730777 17653386159008178320798083)
    ·
      refine ⟨26480079238512267481197125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17653386159008178320798083 26480079238512267481197125)
      ·
        refine ⟨4965014857221050152724461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26480079238512267481197125 4965014857221050152724461)
        ·
          refine ⟨1861880571457893807271673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4965014857221050152724461 1861880571457893807271673)
          ·
            refine ⟨1396410428593420355453755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1861880571457893807271673 1396410428593420355453755)
            ·
              refine ⟨2094615642890130533180633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1396410428593420355453755 2094615642890130533180633)
              ·
                refine ⟨1570961732167597899885475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2094615642890130533180633 1570961732167597899885475)
                ·
                  refine ⟨2356442598251396849828213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1570961732167597899885475 2356442598251396849828213)
                  ·
                    refine ⟨220916493586068454671395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2356442598251396849828213 220916493586068454671395)
                    ·
                      rfl

theorem cell23_1290700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 1, 5].length) (baseStart_1290700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290700 prefixEnd_1290700 := by exact prefixLift 1290700
  have htrace : WordTrace (prefixWord ++ tailWord_1290700) baseStart_1290700 baseEnd_1290700 := by
    simpa [prefixWord, tailWord_1290700, baseEnd_1290700] using wordTrace_append hprefix tailTrace_1290700
  have hstable : (prefixWord ++ tailWord_1290700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290700).length < 2 ^ (prefixWord ++ tailWord_1290700).sum := by decide
  have hdescent : baseEnd_1290700 < baseStart_1290700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290703 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 5, 2, 2]
def baseStart_1290703 : Nat := 118140960795 + 1290703 * 2 ^ 59
def prefixEnd_1290703 : Nat := 4983230072969 + 3 ^ 40 * 1290703 * 2
def baseEnd_1290703 : Nat := 662751021200168852276671

theorem tailTrace_1290703 : CollatzResearch.WordTrace tailWord_1290703 prefixEnd_1290703 662751021200168852276671 := by
  unfold tailWord_1290703
  simp only [CollatzResearch.WordTrace]
  refine ⟨47075805843010940367820763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31383870562007293578547175 47075805843010940367820763)
  ·
    refine ⟨70613708764516410551731145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47075805843010940367820763 70613708764516410551731145)
    ·
      refine ⟨52960281573387307913798359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70613708764516410551731145 52960281573387307913798359)
      ·
        refine ⟨79440422360080961870697539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52960281573387307913798359 79440422360080961870697539)
        ·
          refine ⟨119160633540121442806046309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79440422360080961870697539 119160633540121442806046309)
          ·
            refine ⟨22342618788772770526133683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119160633540121442806046309 22342618788772770526133683)
            ·
              refine ⟨33513928183159155789200525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22342618788772770526133683 33513928183159155789200525)
              ·
                refine ⟨12567723068684683420950197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33513928183159155789200525 12567723068684683420950197)
                ·
                  refine ⟨1178224037689189070714081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12567723068684683420950197 1178224037689189070714081)
                  ·
                    refine ⟨883668028266891803035561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1178224037689189070714081 883668028266891803035561)
                    ·
                      refine ⟨662751021200168852276671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 883668028266891803035561 662751021200168852276671)
                      ·
                        rfl

theorem cell23_1290703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5, 2, 2].length) (baseStart_1290703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290703 prefixEnd_1290703 := by exact prefixLift 1290703
  have htrace : WordTrace (prefixWord ++ tailWord_1290703) baseStart_1290703 baseEnd_1290703 := by
    simpa [prefixWord, tailWord_1290703, baseEnd_1290703] using wordTrace_append hprefix tailTrace_1290703
  have hstable : (prefixWord ++ tailWord_1290703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290703).length < 2 ^ (prefixWord ++ tailWord_1290703).sum := by decide
  have hdescent : baseEnd_1290703 < baseStart_1290703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290729 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 2, 2, 6]
def baseStart_1290729 : Nat := 118140960795 + 1290729 * 2 ^ 59
def prefixEnd_1290729 : Nat := 4983230072969 + 3 ^ 40 * 1290729 * 2
def baseEnd_1290729 : Nat := 662764371697185750551551

theorem tailTrace_1290729 : CollatzResearch.WordTrace tailWord_1290729 prefixEnd_1290729 662764371697185750551551 := by
  unfold tailWord_1290729
  simp only [CollatzResearch.WordTrace]
  refine ⟨47076754140916746808267241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31384502760611164538844827 47076754140916746808267241)
  ·
    refine ⟨35307565605687560106200431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47076754140916746808267241 35307565605687560106200431)
    ·
      refine ⟨52961348408531340159300647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35307565605687560106200431 52961348408531340159300647)
      ·
        refine ⟨79442022612797010238950971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52961348408531340159300647 79442022612797010238950971)
        ·
          refine ⟨119163033919195515358426457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79442022612797010238950971 119163033919195515358426457)
          ·
            refine ⟨89372275439396636518819843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119163033919195515358426457 89372275439396636518819843)
            ·
              refine ⟨134058413159094954778229765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89372275439396636518819843 134058413159094954778229765)
              ·
                refine ⟨25135952467330304020918081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134058413159094954778229765 25135952467330304020918081)
                ·
                  refine ⟨18851964350497728015688561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25135952467330304020918081 18851964350497728015688561)
                  ·
                    refine ⟨14138973262873296011766421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18851964350497728015688561 14138973262873296011766421)
                    ·
                      refine ⟨662764371697185750551551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14138973262873296011766421 662764371697185750551551)
                      ·
                        rfl

theorem cell23_1290729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 2, 6].length) (baseStart_1290729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290729 prefixEnd_1290729 := by exact prefixLift 1290729
  have htrace : WordTrace (prefixWord ++ tailWord_1290729) baseStart_1290729 baseEnd_1290729 := by
    simpa [prefixWord, tailWord_1290729, baseEnd_1290729] using wordTrace_append hprefix tailTrace_1290729
  have hstable : (prefixWord ++ tailWord_1290729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290729).length < 2 ^ (prefixWord ++ tailWord_1290729).sum := by decide
  have hdescent : baseEnd_1290729 < baseStart_1290729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290730 : List Nat := [3, 1, 3, 1, 3, 2, 2, 2, 2, 4]
def baseStart_1290730 : Nat := 118140960795 + 1290730 * 2 ^ 59
def prefixEnd_1290730 : Nat := 4983230072969 + 3 ^ 40 * 1290730 * 2
def baseEnd_1290730 : Nat := 220921628392613415546349

theorem tailTrace_1290730 : CollatzResearch.WordTrace tailWord_1290730 prefixEnd_1290730 220921628392613415546349 := by
  unfold tailWord_1290730
  simp only [CollatzResearch.WordTrace]
  refine ⟨11769197653478280994763411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31384527075942082652702429 11769197653478280994763411)
  ·
    refine ⟨17653796480217421492145117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11769197653478280994763411 17653796480217421492145117)
    ·
      refine ⟨6620173680081533059554419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17653796480217421492145117 6620173680081533059554419)
      ·
        refine ⟨9930260520122299589331629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6620173680081533059554419 9930260520122299589331629)
        ·
          refine ⟨3723847695045862345999361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9930260520122299589331629 3723847695045862345999361)
          ·
            refine ⟨2792885771284396759499521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3723847695045862345999361 2792885771284396759499521)
            ·
              refine ⟨2094664328463297569624641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2792885771284396759499521 2094664328463297569624641)
              ·
                refine ⟨1570998246347473177218481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2094664328463297569624641 1570998246347473177218481)
                ·
                  refine ⟨1178248684760604882913861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1570998246347473177218481 1178248684760604882913861)
                  ·
                    refine ⟨220921628392613415546349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1178248684760604882913861 220921628392613415546349)
                    ·
                      rfl

theorem cell23_1290730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_1290730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290730 prefixEnd_1290730 := by exact prefixLift 1290730
  have htrace : WordTrace (prefixWord ++ tailWord_1290730) baseStart_1290730 baseEnd_1290730 := by
    simpa [prefixWord, tailWord_1290730, baseEnd_1290730] using wordTrace_append hprefix tailTrace_1290730
  have hstable : (prefixWord ++ tailWord_1290730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290730).length < 2 ^ (prefixWord ++ tailWord_1290730).sum := by decide
  have hdescent : baseEnd_1290730 < baseStart_1290730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290736 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 3]
def baseStart_1290736 : Nat := 118140960795 + 1290736 * 2 ^ 59
def prefixEnd_1290736 : Nat := 4983230072969 + 3 ^ 40 * 1290736 * 2
def baseEnd_1290736 : Nat := 662767966061767223164019

theorem tailTrace_1290736 : CollatzResearch.WordTrace tailWord_1290736 prefixEnd_1290736 662767966061767223164019 := by
  unfold tailWord_1290736
  simp only [CollatzResearch.WordTrace]
  refine ⟨23538504725945693501886031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31384672967927591335848041 23538504725945693501886031)
  ·
    refine ⟨35307757088918540252829047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23538504725945693501886031 35307757088918540252829047)
    ·
      refine ⟨52961635633377810379243571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35307757088918540252829047 52961635633377810379243571)
      ·
        refine ⟨79442453450066715568865357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52961635633377810379243571 79442453450066715568865357)
        ·
          refine ⟨29790920043775018338324509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79442453450066715568865357 29790920043775018338324509)
          ·
            refine ⟨11171595016415631876871691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29790920043775018338324509 11171595016415631876871691)
            ·
              refine ⟨16757392524623447815307537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11171595016415631876871691 16757392524623447815307537)
              ·
                refine ⟨12568044393467585861480653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16757392524623447815307537 12568044393467585861480653)
                ·
                  refine ⟨4713016647550344698055245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12568044393467585861480653 4713016647550344698055245)
                  ·
                    refine ⟨1767381242831379261770717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4713016647550344698055245 1767381242831379261770717)
                    ·
                      refine ⟨662767966061767223164019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1767381242831379261770717 662767966061767223164019)
                      ·
                        rfl

theorem cell23_1290736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 3].length) (baseStart_1290736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290736 prefixEnd_1290736 := by exact prefixLift 1290736
  have htrace : WordTrace (prefixWord ++ tailWord_1290736) baseStart_1290736 baseEnd_1290736 := by
    simpa [prefixWord, tailWord_1290736, baseEnd_1290736] using wordTrace_append hprefix tailTrace_1290736
  have hstable : (prefixWord ++ tailWord_1290736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290736).length < 2 ^ (prefixWord ++ tailWord_1290736).sum := by decide
  have hdescent : baseEnd_1290736 < baseStart_1290736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290737 : List Nat := [1, 2, 2, 2, 3, 1, 3, 4, 1, 2, 2]
def baseStart_1290737 : Nat := 118140960795 + 1290737 * 2 ^ 59
def prefixEnd_1290737 : Nat := 4983230072969 + 3 ^ 40 * 1290737 * 2
def baseEnd_1290737 : Nat := 662768479542421719251515

theorem tailTrace_1290737 : CollatzResearch.WordTrace tailWord_1290737 prefixEnd_1290737 662768479542421719251515 := by
  unfold tailWord_1290737
  simp only [CollatzResearch.WordTrace]
  refine ⟨47077045924887764174558465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31384697283258509449705643 47077045924887764174558465)
  ·
    refine ⟨35307784443665823130918849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47077045924887764174558465 35307784443665823130918849)
    ·
      refine ⟨26480838332749367348189137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35307784443665823130918849 26480838332749367348189137)
      ·
        refine ⟨19860628749562025511141853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26480838332749367348189137 19860628749562025511141853)
        ·
          refine ⟨7447735781085759566678195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19860628749562025511141853 7447735781085759566678195)
          ·
            refine ⟨11171603671628639350017293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7447735781085759566678195 11171603671628639350017293)
            ·
              refine ⟨4189351376860739756256485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11171603671628639350017293 4189351376860739756256485)
              ·
                refine ⟨785503383161388704298091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4189351376860739756256485 785503383161388704298091)
                ·
                  refine ⟨1178255074742083056447137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 785503383161388704298091 1178255074742083056447137)
                  ·
                    refine ⟨883691306056562292335353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1178255074742083056447137 883691306056562292335353)
                    ·
                      refine ⟨662768479542421719251515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 883691306056562292335353 662768479542421719251515)
                      ·
                        rfl

theorem cell23_1290737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4, 1, 2, 2].length) (baseStart_1290737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290737 prefixEnd_1290737 := by exact prefixLift 1290737
  have htrace : WordTrace (prefixWord ++ tailWord_1290737) baseStart_1290737 baseEnd_1290737 := by
    simpa [prefixWord, tailWord_1290737, baseEnd_1290737] using wordTrace_append hprefix tailTrace_1290737
  have hstable : (prefixWord ++ tailWord_1290737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290737).length < 2 ^ (prefixWord ++ tailWord_1290737).sum := by decide
  have hdescent : baseEnd_1290737 < baseStart_1290737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290739 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 1, 9]
def baseStart_1290739 : Nat := 118140960795 + 1290739 * 2 ^ 59
def prefixEnd_1290739 : Nat := 4983230072969 + 3 ^ 40 * 1290739 * 2
def baseEnd_1290739 : Nat := 220923168834576903808835

theorem tailTrace_1290739 : CollatzResearch.WordTrace tailWord_1290739 prefixEnd_1290739 220923168834576903808835 := by
  unfold tailWord_1290739
  simp only [CollatzResearch.WordTrace]
  refine ⟨47077118870880518516131271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31384745913920345677420847 47077118870880518516131271)
  ·
    refine ⟨70615678306320777774196907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47077118870880518516131271 70615678306320777774196907)
    ·
      refine ⟨105923517459481166661295361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70615678306320777774196907 105923517459481166661295361)
      ·
        refine ⟨79442638094610874995971521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105923517459481166661295361 79442638094610874995971521)
        ·
          refine ⟨59581978570958156246978641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79442638094610874995971521 59581978570958156246978641)
          ·
            refine ⟨44686483928218617185233981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59581978570958156246978641 44686483928218617185233981)
            ·
              refine ⟨16757431473081981444462743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44686483928218617185233981 16757431473081981444462743)
              ·
                refine ⟨25136147209622972166694115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16757431473081981444462743 25136147209622972166694115)
                ·
                  refine ⟨37704220814434458250041173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25136147209622972166694115 37704220814434458250041173)
                  ·
                    refine ⟨220923168834576903808835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 37704220814434458250041173 220923168834576903808835)
                    ·
                      rfl

theorem cell23_1290739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 9].length) (baseStart_1290739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290739 prefixEnd_1290739 := by exact prefixLift 1290739
  have htrace : WordTrace (prefixWord ++ tailWord_1290739) baseStart_1290739 baseEnd_1290739 := by
    simpa [prefixWord, tailWord_1290739, baseEnd_1290739] using wordTrace_append hprefix tailTrace_1290739
  have hstable : (prefixWord ++ tailWord_1290739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290739).length < 2 ^ (prefixWord ++ tailWord_1290739).sum := by decide
  have hdescent : baseEnd_1290739 < baseStart_1290739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290753 : List Nat := [1, 2, 4, 1, 3, 1, 1, 3, 1, 3, 3]
def baseStart_1290753 : Nat := 118140960795 + 1290753 * 2 ^ 59
def prefixEnd_1290753 : Nat := 4983230072969 + 3 ^ 40 * 1290753 * 2
def baseEnd_1290753 : Nat := 662776695232893656651441

theorem tailTrace_1290753 : CollatzResearch.WordTrace tailWord_1290753 prefixEnd_1290753 662776695232893656651441 := by
  unfold tailWord_1290753
  simp only [CollatzResearch.WordTrace]
  refine ⟨47077629492829798907140913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31385086328553199271427275 47077629492829798907140913)
  ·
    refine ⟨35308222119622349180355685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47077629492829798907140913 35308222119622349180355685)
    ·
      refine ⟨6620291647429190471316691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35308222119622349180355685 6620291647429190471316691)
      ·
        refine ⟨9930437471143785706975037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6620291647429190471316691 9930437471143785706975037)
        ·
          refine ⟨3723914051678919640115639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9930437471143785706975037 3723914051678919640115639)
          ·
            refine ⟨5585871077518379460173459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3723914051678919640115639 5585871077518379460173459)
            ·
              refine ⟨8378806616277569190260189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5585871077518379460173459 8378806616277569190260189)
              ·
                refine ⟨3142052481104088446347571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8378806616277569190260189 3142052481104088446347571)
                ·
                  refine ⟨4713078721656132669521357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3142052481104088446347571 4713078721656132669521357)
                  ·
                    refine ⟨1767404520621049751070509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4713078721656132669521357 1767404520621049751070509)
                    ·
                      refine ⟨662776695232893656651441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1767404520621049751070509 662776695232893656651441)
                      ·
                        rfl

theorem cell23_1290753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_1290753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290753 prefixEnd_1290753 := by exact prefixLift 1290753
  have htrace : WordTrace (prefixWord ++ tailWord_1290753) baseStart_1290753 baseEnd_1290753 := by
    simpa [prefixWord, tailWord_1290753, baseEnd_1290753] using wordTrace_append hprefix tailTrace_1290753
  have hstable : (prefixWord ++ tailWord_1290753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290753).length < 2 ^ (prefixWord ++ tailWord_1290753).sum := by decide
  have hdescent : baseEnd_1290753 < baseStart_1290753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290754 : List Nat := [3, 4, 1, 2, 2, 1, 1, 2, 3, 2, 2]
def baseStart_1290754 : Nat := 118140960795 + 1290754 * 2 ^ 59
def prefixEnd_1290754 : Nat := 4983230072969 + 3 ^ 40 * 1290754 * 2
def baseEnd_1290754 : Nat := 662777208713548152738937

theorem tailTrace_1290754 : CollatzResearch.WordTrace tailWord_1290754 prefixEnd_1290754 662777208713548152738937 := by
  unfold tailWord_1290754
  simp only [CollatzResearch.WordTrace]
  refine ⟨11769416491456544019481829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31385110643884117385284877 11769416491456544019481829)
  ·
    refine ⟨2206765592148102003652843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11769416491456544019481829 2206765592148102003652843)
    ·
      refine ⟨3310148388222153005479265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2206765592148102003652843 3310148388222153005479265)
      ·
        refine ⟨2482611291166614754109449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3310148388222153005479265 2482611291166614754109449)
        ·
          refine ⟨1861958468374961065582087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2482611291166614754109449 1861958468374961065582087)
          ·
            refine ⟨2792937702562441598373131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1861958468374961065582087 2792937702562441598373131)
            ·
              refine ⟨4189406553843662397559697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2792937702562441598373131 4189406553843662397559697)
              ·
                refine ⟨3142054915382746798169773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4189406553843662397559697 3142054915382746798169773)
                ·
                  refine ⟨1178270593268530049313665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3142054915382746798169773 1178270593268530049313665)
                  ·
                    refine ⟨883702944951397536985249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1178270593268530049313665 883702944951397536985249)
                    ·
                      refine ⟨662777208713548152738937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 883702944951397536985249 662777208713548152738937)
                      ·
                        rfl

theorem cell23_1290754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_1290754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290754 prefixEnd_1290754 := by exact prefixLift 1290754
  have htrace : WordTrace (prefixWord ++ tailWord_1290754) baseStart_1290754 baseEnd_1290754 := by
    simpa [prefixWord, tailWord_1290754, baseEnd_1290754] using wordTrace_append hprefix tailTrace_1290754
  have hstable : (prefixWord ++ tailWord_1290754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290754).length < 2 ^ (prefixWord ++ tailWord_1290754).sum := by decide
  have hdescent : baseEnd_1290754 < baseStart_1290754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290787 : List Nat := [1, 1, 1, 4, 4, 3, 1, 2, 2, 1, 3]
def baseStart_1290787 : Nat := 118140960795 + 1290787 * 2 ^ 59
def prefixEnd_1290787 : Nat := 4983230072969 + 3 ^ 40 * 1290787 * 2
def baseEnd_1290787 : Nat := 662794153575146523626285

theorem tailTrace_1290787 : CollatzResearch.WordTrace tailWord_1290787 prefixEnd_1290787 662794153575146523626285 := by
  unfold tailWord_1290787
  simp only [CollatzResearch.WordTrace]
  refine ⟨47078869574706622713878615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31385913049804415142585743 47078869574706622713878615)
  ·
    refine ⟨70618304362059934070817923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47078869574706622713878615 70618304362059934070817923)
    ·
      refine ⟨105927456543089901106226885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70618304362059934070817923 105927456543089901106226885)
      ·
        refine ⟨19861398101829356457417541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105927456543089901106226885 19861398101829356457417541)
        ·
          refine ⟨3724012144093004335765789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19861398101829356457417541 3724012144093004335765789)
          ·
            refine ⟨1396504554034876625912171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3724012144093004335765789 1396504554034876625912171)
            ·
              refine ⟨2094756831052314938868257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1396504554034876625912171 2094756831052314938868257)
              ·
                refine ⟨1571067623289236204151193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2094756831052314938868257 1571067623289236204151193)
                ·
                  refine ⟨1178300717466927153113395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1571067623289236204151193 1178300717466927153113395)
                  ·
                    refine ⟨1767451076200390729670093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1178300717466927153113395 1767451076200390729670093)
                    ·
                      refine ⟨662794153575146523626285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1767451076200390729670093 662794153575146523626285)
                      ·
                        rfl

theorem cell23_1290787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_1290787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290787 prefixEnd_1290787 := by exact prefixLift 1290787
  have htrace : WordTrace (prefixWord ++ tailWord_1290787) baseStart_1290787 baseEnd_1290787 := by
    simpa [prefixWord, tailWord_1290787, baseEnd_1290787] using wordTrace_append hprefix tailTrace_1290787
  have hstable : (prefixWord ++ tailWord_1290787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290787).length < 2 ^ (prefixWord ++ tailWord_1290787).sum := by decide
  have hdescent : baseEnd_1290787 < baseStart_1290787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290796 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 3]
def baseStart_1290796 : Nat := 118140960795 + 1290796 * 2 ^ 59
def prefixEnd_1290796 : Nat := 4983230072969 + 3 ^ 40 * 1290796 * 2
def baseEnd_1290796 : Nat := 662798774901036988413743

theorem tailTrace_1290796 : CollatzResearch.WordTrace tailWord_1290796 prefixEnd_1290796 662798774901036988413743 := by
  unfold tailWord_1290796
  simp only [CollatzResearch.WordTrace]
  refine ⟨23539598915837008625478121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31386131887782678167304161 23539598915837008625478121)
  ·
    refine ⟨17654699186877756469108591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23539598915837008625478121 17654699186877756469108591)
    ·
      refine ⟨26482048780316634703662887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17654699186877756469108591 26482048780316634703662887)
      ·
        refine ⟨39723073170474952055494331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26482048780316634703662887 39723073170474952055494331)
        ·
          refine ⟨59584609755712428083241497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39723073170474952055494331 59584609755712428083241497)
          ·
            refine ⟨44688457316784321062431123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59584609755712428083241497 44688457316784321062431123)
            ·
              refine ⟨67032685975176481593646685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44688457316784321062431123 67032685975176481593646685)
              ·
                refine ⟨25137257240691180597617507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67032685975176481593646685 25137257240691180597617507)
                ·
                  refine ⟨37705885861036770896426261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25137257240691180597617507 37705885861036770896426261)
                  ·
                    refine ⟨1767463399736098635769981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37705885861036770896426261 1767463399736098635769981)
                    ·
                      refine ⟨662798774901036988413743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1767463399736098635769981 662798774901036988413743)
                      ·
                        rfl

theorem cell23_1290796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 3].length) (baseStart_1290796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290796 prefixEnd_1290796 := by exact prefixLift 1290796
  have htrace : WordTrace (prefixWord ++ tailWord_1290796) baseStart_1290796 baseEnd_1290796 := by
    simpa [prefixWord, tailWord_1290796, baseEnd_1290796] using wordTrace_append hprefix tailTrace_1290796
  have hstable : (prefixWord ++ tailWord_1290796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290796).length < 2 ^ (prefixWord ++ tailWord_1290796).sum := by decide
  have hdescent : baseEnd_1290796 < baseStart_1290796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290804 : List Nat := [2, 5, 1, 3, 1, 2, 1, 1, 1, 3, 3]
def baseStart_1290804 : Nat := 118140960795 + 1290804 * 2 ^ 59
def prefixEnd_1290804 : Nat := 4983230072969 + 3 ^ 40 * 1290804 * 2
def baseEnd_1290804 : Nat := 662802882746272957113707

theorem tailTrace_1290804 : CollatzResearch.WordTrace tailWord_1290804 prefixEnd_1290804 662802882746272957113707 := by
  unfold tailWord_1290804
  simp only [CollatzResearch.WordTrace]
  refine ⟨23539744807822517308623733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31386326410430023078164977 23539744807822517308623733)
  ·
    refine ⟨2206851075733360997683475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23539744807822517308623733 2206851075733360997683475)
    ·
      refine ⟨3310276613600041496525213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2206851075733360997683475 3310276613600041496525213)
      ·
        refine ⟨1241353730100015561196955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3310276613600041496525213 1241353730100015561196955)
        ·
          refine ⟨1862030595150023341795433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1241353730100015561196955 1862030595150023341795433)
          ·
            refine ⟨1396522946362517506346575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1862030595150023341795433 1396522946362517506346575)
            ·
              refine ⟨2094784419543776259519863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1396522946362517506346575 2094784419543776259519863)
              ·
                refine ⟨3142176629315664389279795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2094784419543776259519863 3142176629315664389279795)
                ·
                  refine ⟨4713264943973496583919693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3142176629315664389279795 4713264943973496583919693)
                  ·
                    refine ⟨1767474353990061218969885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4713264943973496583919693 1767474353990061218969885)
                    ·
                      refine ⟨662802882746272957113707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1767474353990061218969885 662802882746272957113707)
                      ·
                        rfl

theorem cell23_1290804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_1290804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290804 prefixEnd_1290804 := by exact prefixLift 1290804
  have htrace : WordTrace (prefixWord ++ tailWord_1290804) baseStart_1290804 baseEnd_1290804 := by
    simpa [prefixWord, tailWord_1290804, baseEnd_1290804] using wordTrace_append hprefix tailTrace_1290804
  have hstable : (prefixWord ++ tailWord_1290804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290804).length < 2 ^ (prefixWord ++ tailWord_1290804).sum := by decide
  have hdescent : baseEnd_1290804 < baseStart_1290804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290810 : List Nat := [3, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2]
def baseStart_1290810 : Nat := 118140960795 + 1290810 * 2 ^ 59
def prefixEnd_1290810 : Nat := 4983230072969 + 3 ^ 40 * 1290810 * 2
def baseEnd_1290810 : Nat := 662805963630199933638679

theorem tailTrace_1290810 : CollatzResearch.WordTrace tailWord_1290810 prefixEnd_1290810 662805963630199933638679 := by
  unfold tailWord_1290810
  simp only [CollatzResearch.WordTrace]
  refine ⟨11769927113405824410491471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31386472302415531761310589 11769927113405824410491471)
  ·
    refine ⟨17654890670108736615737207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11769927113405824410491471 17654890670108736615737207)
    ·
      refine ⟨26482336005163104923605811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17654890670108736615737207 26482336005163104923605811)
      ·
        refine ⟨39723504007744657385408717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26482336005163104923605811 39723504007744657385408717)
        ·
          refine ⟨14896314002904246519528269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39723504007744657385408717 14896314002904246519528269)
          ·
            refine ⟨5586117751089092444823101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14896314002904246519528269 5586117751089092444823101)
            ·
              refine ⟨2094794156658409666808663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5586117751089092444823101 2094794156658409666808663)
              ·
                refine ⟨3142191234987614500212995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2094794156658409666808663 3142191234987614500212995)
                ·
                  refine ⟨4713286852481421750319493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3142191234987614500212995 4713286852481421750319493)
                  ·
                    refine ⟨883741284840266578184905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4713286852481421750319493 883741284840266578184905)
                    ·
                      refine ⟨662805963630199933638679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 883741284840266578184905 662805963630199933638679)
                      ·
                        rfl

theorem cell23_1290810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2].length) (baseStart_1290810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290810 prefixEnd_1290810 := by exact prefixLift 1290810
  have htrace : WordTrace (prefixWord ++ tailWord_1290810) baseStart_1290810 baseEnd_1290810 := by
    simpa [prefixWord, tailWord_1290810, baseEnd_1290810] using wordTrace_append hprefix tailTrace_1290810
  have hstable : (prefixWord ++ tailWord_1290810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290810).length < 2 ^ (prefixWord ++ tailWord_1290810).sum := by decide
  have hdescent : baseEnd_1290810 < baseStart_1290810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290816 : List Nat := [2, 1, 1, 2, 2, 2, 4, 2, 7]
def baseStart_1290816 : Nat := 118140960795 + 1290816 * 2 ^ 59
def prefixEnd_1290816 : Nat := 4983230072969 + 3 ^ 40 * 1290816 * 2
def baseEnd_1290816 : Nat := 73645449390458545573739

theorem tailTrace_1290816 : CollatzResearch.WordTrace tailWord_1290816 prefixEnd_1290816 73645449390458545573739 := by
  unfold tailWord_1290816
  simp only [CollatzResearch.WordTrace]
  refine ⟨23539963645800780333342151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31386618194401040444456201 23539963645800780333342151)
  ·
    refine ⟨35309945468701170500013227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23539963645800780333342151 35309945468701170500013227)
    ·
      refine ⟨52964918203051755750019841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35309945468701170500013227 52964918203051755750019841)
      ·
        refine ⟨39723688652288816812514881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52964918203051755750019841 39723688652288816812514881)
        ·
          refine ⟨29792766489216612609386161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39723688652288816812514881 29792766489216612609386161)
          ·
            refine ⟨22344574866912459457039621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29792766489216612609386161 22344574866912459457039621)
            ·
              refine ⟨4189607787546086148194929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22344574866912459457039621 4189607787546086148194929)
              ·
                refine ⟨3142205840659564611146197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4189607787546086148194929 3142205840659564611146197)
                ·
                  refine ⟨73645449390458545573739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3142205840659564611146197 73645449390458545573739)
                  ·
                    rfl

theorem cell23_1290816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 7].length) (baseStart_1290816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290816 prefixEnd_1290816 := by exact prefixLift 1290816
  have htrace : WordTrace (prefixWord ++ tailWord_1290816) baseStart_1290816 baseEnd_1290816 := by
    simpa [prefixWord, tailWord_1290816, baseEnd_1290816] using wordTrace_append hprefix tailTrace_1290816
  have hstable : (prefixWord ++ tailWord_1290816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290816).length < 2 ^ (prefixWord ++ tailWord_1290816).sum := by decide
  have hdescent : baseEnd_1290816 < baseStart_1290816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290861 : List Nat := [1, 5, 1, 1, 3, 3, 2, 1, 2, 2, 2]
def baseStart_1290861 : Nat := 118140960795 + 1290861 * 2 ^ 59
def prefixEnd_1290861 : Nat := 4983230072969 + 3 ^ 40 * 1290861 * 2
def baseEnd_1290861 : Nat := 662832151143579234100945

theorem tailTrace_1290861 : CollatzResearch.WordTrace tailWord_1290861 prefixEnd_1290861 662832151143579234100945 := by
  unfold tailWord_1290861
  simp only [CollatzResearch.WordTrace]
  refine ⟨47081568576438533352072437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31387712384292355568048291 47081568576438533352072437)
  ·
    refine ⟨4413897054041112501756791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47081568576438533352072437 4413897054041112501756791)
    ·
      refine ⟨6620845581061668752635187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4413897054041112501756791 6620845581061668752635187)
      ·
        refine ⟨9931268371592503128952781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6620845581061668752635187 9931268371592503128952781)
        ·
          refine ⟨3724225639347188673357293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9931268371592503128952781 3724225639347188673357293)
          ·
            refine ⟨1396584614755195752508985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3724225639347188673357293 1396584614755195752508985)
            ·
              refine ⟨1047438461066396814381739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1396584614755195752508985 1047438461066396814381739)
              ·
                refine ⟨1571157691599595221572609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1047438461066396814381739 1571157691599595221572609)
                ·
                  refine ⟨1178368268699696416179457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1571157691599595221572609 1178368268699696416179457)
                  ·
                    refine ⟨883776201524772312134593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1178368268699696416179457 883776201524772312134593)
                    ·
                      refine ⟨662832151143579234100945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 883776201524772312134593 662832151143579234100945)
                      ·
                        rfl

theorem cell23_1290861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_1290861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290861 prefixEnd_1290861 := by exact prefixLift 1290861
  have htrace : WordTrace (prefixWord ++ tailWord_1290861) baseStart_1290861 baseEnd_1290861 := by
    simpa [prefixWord, tailWord_1290861, baseEnd_1290861] using wordTrace_append hprefix tailTrace_1290861
  have hstable : (prefixWord ++ tailWord_1290861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290861).length < 2 ^ (prefixWord ++ tailWord_1290861).sum := by decide
  have hdescent : baseEnd_1290861 < baseStart_1290861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290876 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 2, 8]
def baseStart_1290876 : Nat := 118140960795 + 1290876 * 2 ^ 59
def prefixEnd_1290876 : Nat := 4983230072969 + 3 ^ 40 * 1290876 * 2
def baseEnd_1290876 : Nat := 220946617784465558471125

theorem tailTrace_1290876 : CollatzResearch.WordTrace tailWord_1290876 prefixEnd_1290876 220946617784465558471125 := by
  unfold tailWord_1290876
  simp only [CollatzResearch.WordTrace]
  refine ⟨23541057835692095456934241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31388077114256127275912321 23541057835692095456934241)
  ·
    refine ⟨17655793376769071592700681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23541057835692095456934241 17655793376769071592700681)
    ·
      refine ⟨13241845032576803694525511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17655793376769071592700681 13241845032576803694525511)
      ·
        refine ⟨19862767548865205541788267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13241845032576803694525511 19862767548865205541788267)
        ·
          refine ⟨29794151323297808312682401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19862767548865205541788267 29794151323297808312682401)
          ·
            refine ⟨22345613492473356234511801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29794151323297808312682401 22345613492473356234511801)
            ·
              refine ⟨16759210119355017175883851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22345613492473356234511801 16759210119355017175883851)
              ·
                refine ⟨25138815179032525763825777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16759210119355017175883851 25138815179032525763825777)
                ·
                  refine ⟨18854111384274394322869333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25138815179032525763825777 18854111384274394322869333)
                  ·
                    refine ⟨220946617784465558471125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18854111384274394322869333 220946617784465558471125)
                    ·
                      rfl

theorem cell23_1290876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_1290876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290876 prefixEnd_1290876 := by exact prefixLift 1290876
  have htrace : WordTrace (prefixWord ++ tailWord_1290876) baseStart_1290876 baseEnd_1290876 := by
    simpa [prefixWord, tailWord_1290876, baseEnd_1290876] using wordTrace_append hprefix tailTrace_1290876
  have hstable : (prefixWord ++ tailWord_1290876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290876).length < 2 ^ (prefixWord ++ tailWord_1290876).sum := by decide
  have hdescent : baseEnd_1290876 < baseStart_1290876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290883 : List Nat := [1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 4]
def baseStart_1290883 : Nat := 118140960795 + 1290883 * 2 ^ 59
def prefixEnd_1290883 : Nat := 4983230072969 + 3 ^ 40 * 1290883 * 2
def baseEnd_1290883 : Nat := 662843447717978148025843

theorem tailTrace_1290883 : CollatzResearch.WordTrace tailWord_1290883 prefixEnd_1290883 662843447717978148025843 := by
  unfold tailWord_1290883
  simp only [CollatzResearch.WordTrace]
  refine ⟨47082370982358831109373303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31388247321572554072915535 47082370982358831109373303)
  ·
    refine ⟨70623556473538246664059955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47082370982358831109373303 70623556473538246664059955)
    ·
      refine ⟨105935334710307369996089933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70623556473538246664059955 105935334710307369996089933)
      ·
        refine ⟨39725750516365263748533725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105935334710307369996089933 39725750516365263748533725)
        ·
          refine ⟨14897156443636973905700147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39725750516365263748533725 14897156443636973905700147)
          ·
            refine ⟨22345734665455460858550221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14897156443636973905700147 22345734665455460858550221)
            ·
              refine ⟨8379650499545797821956333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22345734665455460858550221 8379650499545797821956333)
              ·
                refine ⟨3142368937329674183233625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8379650499545797821956333 3142368937329674183233625)
                ·
                  refine ⟨2356776702997255637425219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3142368937329674183233625 2356776702997255637425219)
                  ·
                    refine ⟨3535165054495883456137829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2356776702997255637425219 3535165054495883456137829)
                    ·
                      refine ⟨662843447717978148025843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3535165054495883456137829 662843447717978148025843)
                      ·
                        rfl

theorem cell23_1290883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_1290883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290883 prefixEnd_1290883 := by exact prefixLift 1290883
  have htrace : WordTrace (prefixWord ++ tailWord_1290883) baseStart_1290883 baseEnd_1290883 := by
    simpa [prefixWord, tailWord_1290883, baseEnd_1290883] using wordTrace_append hprefix tailTrace_1290883
  have hstable : (prefixWord ++ tailWord_1290883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290883).length < 2 ^ (prefixWord ++ tailWord_1290883).sum := by decide
  have hdescent : baseEnd_1290883 < baseStart_1290883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290957 : List Nat := [1, 6, 2, 1, 2, 1, 1, 1, 8]
def baseStart_1290957 : Nat := 118140960795 + 1290957 * 2 ^ 59
def prefixEnd_1290957 : Nat := 4983230072969 + 3 ^ 40 * 1290957 * 2
def baseEnd_1290957 : Nat := 73653493920712317611167

theorem tailTrace_1290957 : CollatzResearch.WordTrace tailWord_1290957 prefixEnd_1290957 73653493920712317611167 := by
  unfold tailWord_1290957
  simp only [CollatzResearch.WordTrace]
  refine ⟨47085069984090741747567125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31390046656060494498378083 47085069984090741747567125)
  ·
    refine ⟨2207112655504253519417209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 47085069984090741747567125 2207112655504253519417209)
    ·
      refine ⟨1655334491628190139562907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2207112655504253519417209 1655334491628190139562907)
      ·
        refine ⟨2483001737442285209344361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1655334491628190139562907 2483001737442285209344361)
        ·
          refine ⟨1862251303081713907008271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2483001737442285209344361 1862251303081713907008271)
          ·
            refine ⟨2793376954622570860512407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1862251303081713907008271 2793376954622570860512407)
            ·
              refine ⟨4190065431933856290768611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2793376954622570860512407 4190065431933856290768611)
              ·
                refine ⟨6285098147900784436152917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4190065431933856290768611 6285098147900784436152917)
                ·
                  refine ⟨73653493920712317611167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6285098147900784436152917 73653493920712317611167)
                  ·
                    rfl

theorem cell23_1290957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_1290957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290957 prefixEnd_1290957 := by exact prefixLift 1290957
  have htrace : WordTrace (prefixWord ++ tailWord_1290957) baseStart_1290957 baseEnd_1290957 := by
    simpa [prefixWord, tailWord_1290957, baseEnd_1290957] using wordTrace_append hprefix tailTrace_1290957
  have hstable : (prefixWord ++ tailWord_1290957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290957).length < 2 ^ (prefixWord ++ tailWord_1290957).sum := by decide
  have hdescent : baseEnd_1290957 < baseStart_1290957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290967 : List Nat := [1, 1, 3, 2, 1, 5, 2, 1, 3, 1, 3]
def baseStart_1290967 : Nat := 118140960795 + 1290967 * 2 ^ 59
def prefixEnd_1290967 : Nat := 4983230072969 + 3 ^ 40 * 1290967 * 2
def baseEnd_1290967 : Nat := 662886580092955819375457

theorem tailTrace_1290967 : CollatzResearch.WordTrace tailWord_1290967 prefixEnd_1290967 662886580092955819375457 := by
  unfold tailWord_1290967
  simp only [CollatzResearch.WordTrace]
  refine ⟨47085434714054513455431155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31390289809369675636954103 47085434714054513455431155)
  ·
    refine ⟨70628152071081770183146733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47085434714054513455431155 70628152071081770183146733)
    ·
      refine ⟨26485557026655663818680025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70628152071081770183146733 26485557026655663818680025)
      ·
        refine ⟨19864167769991747864010019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26485557026655663818680025 19864167769991747864010019)
        ·
          refine ⟨29796251654987621796015029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19864167769991747864010019 29796251654987621796015029)
          ·
            refine ⟨2793398592655089543376409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29796251654987621796015029 2793398592655089543376409)
            ·
              refine ⟨2095048944491317157532307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2793398592655089543376409 2095048944491317157532307)
              ·
                refine ⟨3142573416736975736298461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2095048944491317157532307 3142573416736975736298461)
                ·
                  refine ⟨1178465031276365901111923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3142573416736975736298461 1178465031276365901111923)
                  ·
                    refine ⟨1767697546914548851667885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1178465031276365901111923 1767697546914548851667885)
                    ·
                      refine ⟨662886580092955819375457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1767697546914548851667885 662886580092955819375457)
                      ·
                        rfl

theorem cell23_1290967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_1290967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290967 prefixEnd_1290967 := by exact prefixLift 1290967
  have htrace : WordTrace (prefixWord ++ tailWord_1290967) baseStart_1290967 baseEnd_1290967 := by
    simpa [prefixWord, tailWord_1290967, baseEnd_1290967] using wordTrace_append hprefix tailTrace_1290967
  have hstable : (prefixWord ++ tailWord_1290967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290967).length < 2 ^ (prefixWord ++ tailWord_1290967).sum := by decide
  have hdescent : baseEnd_1290967 < baseStart_1290967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290993 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 3, 1, 5]
def baseStart_1290993 : Nat := 118140960795 + 1290993 * 2 ^ 59
def prefixEnd_1290993 : Nat := 4983230072969 + 3 ^ 40 * 1290993 * 2
def baseEnd_1290993 : Nat := 662899930589972717650337

theorem tailTrace_1290993 : CollatzResearch.WordTrace tailWord_1290993 prefixEnd_1290993 662899930589972717650337 := by
  unfold tailWord_1290993
  simp only [CollatzResearch.WordTrace]
  refine ⟨47086383011960319895877633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31390922007973546597251755 47086383011960319895877633)
  ·
    refine ⟨35314787258970239921908225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47086383011960319895877633 35314787258970239921908225)
    ·
      refine ⟨26486090444227679941431169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35314787258970239921908225 26486090444227679941431169)
      ·
        refine ⟨19864567833170759956073377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26486090444227679941431169 19864567833170759956073377)
        ·
          refine ⟨14898425874878069967055033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19864567833170759956073377 14898425874878069967055033)
          ·
            refine ⟨11173819406158552475291275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14898425874878069967055033 11173819406158552475291275)
            ·
              refine ⟨16760729109237828712936913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11173819406158552475291275 16760729109237828712936913)
              ·
                refine ⟨12570546831928371534702685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16760729109237828712936913 12570546831928371534702685)
                ·
                  refine ⟨4713955061973139325513507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12570546831928371534702685 4713955061973139325513507)
                  ·
                    refine ⟨7070932592959708988270261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4713955061973139325513507 7070932592959708988270261)
                    ·
                      refine ⟨662899930589972717650337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7070932592959708988270261 662899930589972717650337)
                      ·
                        rfl

theorem cell23_1290993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_1290993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1290993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1290993 prefixEnd_1290993 := by exact prefixLift 1290993
  have htrace : WordTrace (prefixWord ++ tailWord_1290993) baseStart_1290993 baseEnd_1290993 := by
    simpa [prefixWord, tailWord_1290993, baseEnd_1290993] using wordTrace_append hprefix tailTrace_1290993
  have hstable : (prefixWord ++ tailWord_1290993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290993).length < 2 ^ (prefixWord ++ tailWord_1290993).sum := by decide
  have hdescent : baseEnd_1290993 < baseStart_1290993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291090 : List Nat := [3, 2, 2, 1, 1, 2, 3, 1, 2, 6]
def baseStart_1291090 : Nat := 118140960795 + 1291090 * 2 ^ 59
def prefixEnd_1291090 : Nat := 4983230072969 + 3 ^ 40 * 1291090 * 2
def baseEnd_1291090 : Nat := 220983246071152946045797

theorem tailTrace_1291090 : CollatzResearch.WordTrace tailWord_1291090 prefixEnd_1291090 220983246071152946045797 := by
  unfold tailWord_1291090
  simp only [CollatzResearch.WordTrace]
  refine ⟨11772480223152226365539681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31393280595072603641439149 11772480223152226365539681)
  ·
    refine ⟨8829360167364169774154761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11772480223152226365539681 8829360167364169774154761)
    ·
      refine ⟨6622020125523127330616071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8829360167364169774154761 6622020125523127330616071)
      ·
        refine ⟨9933030188284690995924107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6622020125523127330616071 9933030188284690995924107)
        ·
          refine ⟨14899545282427036493886161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9933030188284690995924107 14899545282427036493886161)
          ·
            refine ⟨11174658961820277370414621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14899545282427036493886161 11174658961820277370414621)
            ·
              refine ⟨4190497110682604013905483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11174658961820277370414621 4190497110682604013905483)
              ·
                refine ⟨6285745666023906020858225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4190497110682604013905483 6285745666023906020858225)
                ·
                  refine ⟨4714309249517929515643669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6285745666023906020858225 4714309249517929515643669)
                  ·
                    refine ⟨220983246071152946045797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4714309249517929515643669 220983246071152946045797)
                    ·
                      rfl

theorem cell23_1291090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_1291090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291090 prefixEnd_1291090 := by exact prefixLift 1291090
  have htrace : WordTrace (prefixWord ++ tailWord_1291090) baseStart_1291090 baseEnd_1291090 := by
    simpa [prefixWord, tailWord_1291090, baseEnd_1291090] using wordTrace_append hprefix tailTrace_1291090
  have hstable : (prefixWord ++ tailWord_1291090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291090).length < 2 ^ (prefixWord ++ tailWord_1291090).sum := by decide
  have hdescent : baseEnd_1291090 < baseStart_1291090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291097 : List Nat := [1, 2, 1, 2, 2, 4, 1, 3, 1, 4, 2]
def baseStart_1291097 : Nat := 118140960795 + 1291097 * 2 ^ 59
def prefixEnd_1291097 : Nat := 4983230072969 + 3 ^ 40 * 1291097 * 2
def baseEnd_1291097 : Nat := 662953332578040310749859

theorem tailTrace_1291097 : CollatzResearch.WordTrace tailWord_1291097 prefixEnd_1291097 662953332578040310749859 := by
  unfold tailWord_1291097
  simp only [CollatzResearch.WordTrace]
  refine ⟨47090176203583545657663545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31393450802389030438442363 47090176203583545657663545)
  ·
    refine ⟨35317632152687659243247659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47090176203583545657663545 35317632152687659243247659)
    ·
      refine ⟨52976448229031488864871489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35317632152687659243247659 52976448229031488864871489)
      ·
        refine ⟨39732336171773616648653617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52976448229031488864871489 39732336171773616648653617)
        ·
          refine ⟨29799252128830212486490213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39732336171773616648653617 29799252128830212486490213)
          ·
            refine ⟨5587359774155664841216915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29799252128830212486490213 5587359774155664841216915)
            ·
              refine ⟨8381039661233497261825373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5587359774155664841216915 8381039661233497261825373)
              ·
                refine ⟨3142889872962561473184515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8381039661233497261825373 3142889872962561473184515)
                ·
                  refine ⟨4714334809443842209776773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3142889872962561473184515 4714334809443842209776773)
                  ·
                    refine ⟨883937776770720414333145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4714334809443842209776773 883937776770720414333145)
                    ·
                      refine ⟨662953332578040310749859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 883937776770720414333145 662953332578040310749859)
                      ·
                        rfl

theorem cell23_1291097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 4, 2].length) (baseStart_1291097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291097 prefixEnd_1291097 := by exact prefixLift 1291097
  have htrace : WordTrace (prefixWord ++ tailWord_1291097) baseStart_1291097 baseEnd_1291097 := by
    simpa [prefixWord, tailWord_1291097, baseEnd_1291097] using wordTrace_append hprefix tailTrace_1291097
  have hstable : (prefixWord ++ tailWord_1291097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291097).length < 2 ^ (prefixWord ++ tailWord_1291097).sum := by decide
  have hdescent : baseEnd_1291097 < baseStart_1291097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291113 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 3, 2, 7]
def baseStart_1291113 : Nat := 118140960795 + 1291113 * 2 ^ 59
def prefixEnd_1291113 : Nat := 4983230072969 + 3 ^ 40 * 1291113 * 2
def baseEnd_1291113 : Nat := 662961548268512248149785

theorem tailTrace_1291113 : CollatzResearch.WordTrace tailWord_1291113 prefixEnd_1291113 662961548268512248149785 := by
  unfold tailWord_1291113
  simp only [CollatzResearch.WordTrace]
  refine ⟨47090759771525580390245993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31393839847683720260163995 47090759771525580390245993)
  ·
    refine ⟨35318069828644185292684495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47090759771525580390245993 35318069828644185292684495)
    ·
      refine ⟨52977104742966277939026743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35318069828644185292684495 52977104742966277939026743)
      ·
        refine ⟨79465657114449416908540115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52977104742966277939026743 79465657114449416908540115)
        ·
          refine ⟨119198485671674125362810173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79465657114449416908540115 119198485671674125362810173)
          ·
            refine ⟨44699432126877797011053815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119198485671674125362810173 44699432126877797011053815)
            ·
              refine ⟨67049148190316695516580723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44699432126877797011053815 67049148190316695516580723)
              ·
                refine ⟨100573722285475043274871085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67049148190316695516580723 100573722285475043274871085)
                ·
                  refine ⟨37715145857053141228076657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100573722285475043274871085 37715145857053141228076657)
                  ·
                    refine ⟨28286359392789855921057493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37715145857053141228076657 28286359392789855921057493)
                    ·
                      refine ⟨662961548268512248149785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28286359392789855921057493 662961548268512248149785)
                      ·
                        rfl

theorem cell23_1291113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 2, 7].length) (baseStart_1291113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291113 prefixEnd_1291113 := by exact prefixLift 1291113
  have htrace : WordTrace (prefixWord ++ tailWord_1291113) baseStart_1291113 baseEnd_1291113 := by
    simpa [prefixWord, tailWord_1291113, baseEnd_1291113] using wordTrace_append hprefix tailTrace_1291113
  have hstable : (prefixWord ++ tailWord_1291113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291113).length < 2 ^ (prefixWord ++ tailWord_1291113).sum := by decide
  have hdescent : baseEnd_1291113 < baseStart_1291113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291187 : List Nat := [1, 1, 1, 2, 3, 1, 2, 4, 2, 4, 2]
def baseStart_1291187 : Nat := 118140960795 + 1291187 * 2 ^ 59
def prefixEnd_1291187 : Nat := 4983230072969 + 3 ^ 40 * 1291187 * 2
def baseEnd_1291187 : Nat := 662999545836944958624445

theorem tailTrace_1291187 : CollatzResearch.WordTrace tailWord_1291187 prefixEnd_1291187 662999545836944958624445 := by
  unfold tailWord_1291187
  simp only [CollatzResearch.WordTrace]
  refine ⟨47093458773257491028439815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31395639182171660685626543 47093458773257491028439815)
  ·
    refine ⟨70640188159886236542659723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47093458773257491028439815 70640188159886236542659723)
    ·
      refine ⟨105960282239829354813989585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70640188159886236542659723 105960282239829354813989585)
      ·
        refine ⟨79470211679872016110492189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105960282239829354813989585 79470211679872016110492189)
        ·
          refine ⟨29801329379952006041434571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79470211679872016110492189 29801329379952006041434571)
          ·
            refine ⟨44701994069928009062151857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29801329379952006041434571 44701994069928009062151857)
            ·
              refine ⟨33526495552446006796613893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44701994069928009062151857 33526495552446006796613893)
              ·
                refine ⟨6286217916083626274365105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33526495552446006796613893 6286217916083626274365105)
                ·
                  refine ⟨4714663437062719705773829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6286217916083626274365105 4714663437062719705773829)
                  ·
                    refine ⟨883999394449259944832593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4714663437062719705773829 883999394449259944832593)
                    ·
                      refine ⟨662999545836944958624445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 883999394449259944832593 662999545836944958624445)
                      ·
                        rfl

theorem cell23_1291187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 4, 2].length) (baseStart_1291187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291187 prefixEnd_1291187 := by exact prefixLift 1291187
  have htrace : WordTrace (prefixWord ++ tailWord_1291187) baseStart_1291187 baseEnd_1291187 := by
    simpa [prefixWord, tailWord_1291187, baseEnd_1291187] using wordTrace_append hprefix tailTrace_1291187
  have hstable : (prefixWord ++ tailWord_1291187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291187).length < 2 ^ (prefixWord ++ tailWord_1291187).sum := by decide
  have hdescent : baseEnd_1291187 < baseStart_1291187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291188 : List Nat := [2, 5, 2, 1, 1, 2, 3, 2, 5]
def baseStart_1291188 : Nat := 118140960795 + 1291188 * 2 ^ 59
def prefixEnd_1291188 : Nat := 4983230072969 + 3 ^ 40 * 1291188 * 2
def baseEnd_1291188 : Nat := 73666673257511050523549

theorem tailTrace_1291188 : CollatzResearch.WordTrace tailWord_1291188 prefixEnd_1291188 73666673257511050523549 := by
  unfold tailWord_1291188
  simp only [CollatzResearch.WordTrace]
  refine ⟨23546747623126934099613109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31395663497502578799484145 23546747623126934099613109)
  ·
    refine ⟨2207507589668150071838729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23546747623126934099613109 2207507589668150071838729)
    ·
      refine ⟨1655630692251112553879047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2207507589668150071838729 1655630692251112553879047)
      ·
        refine ⟨2483446038376668830818571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1655630692251112553879047 2483446038376668830818571)
        ·
          refine ⟨3725169057565003246227857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2483446038376668830818571 3725169057565003246227857)
          ·
            refine ⟨2793876793173752434670893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3725169057565003246227857 2793876793173752434670893)
            ·
              refine ⟨1047703797440157163001585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2793876793173752434670893 1047703797440157163001585)
              ·
                refine ⟨785777848080117872251189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1047703797440157163001585 785777848080117872251189)
                ·
                  refine ⟨73666673257511050523549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 785777848080117872251189 73666673257511050523549)
                  ·
                    rfl

theorem cell23_1291188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_1291188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291188 prefixEnd_1291188 := by exact prefixLift 1291188
  have htrace : WordTrace (prefixWord ++ tailWord_1291188) baseStart_1291188 baseEnd_1291188 := by
    simpa [prefixWord, tailWord_1291188, baseEnd_1291188] using wordTrace_append hprefix tailTrace_1291188
  have hstable : (prefixWord ++ tailWord_1291188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291188).length < 2 ^ (prefixWord ++ tailWord_1291188).sum := by decide
  have hdescent : baseEnd_1291188 < baseStart_1291188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291224 : List Nat := [2, 1, 2, 2, 2, 4, 2, 1, 2, 2, 3]
def baseStart_1291224 : Nat := 118140960795 + 1291224 * 2 ^ 59
def prefixEnd_1291224 : Nat := 4983230072969 + 3 ^ 40 * 1291224 * 2
def baseEnd_1291224 : Nat := 663018544621161313861775

theorem tailTrace_1291224 : CollatzResearch.WordTrace tailWord_1291224 prefixEnd_1291224 663018544621161313861775 := by
  unfold tailWord_1291224
  simp only [CollatzResearch.WordTrace]
  refine ⟨23547404137061723173768363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31396538849415630898357817 23547404137061723173768363)
  ·
    refine ⟨35321106205592584760652545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23547404137061723173768363 35321106205592584760652545)
    ·
      refine ⟨26490829654194438570489409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35321106205592584760652545 26490829654194438570489409)
      ·
        refine ⟨19868122240645828927867057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26490829654194438570489409 19868122240645828927867057)
        ·
          refine ⟨14901091680484371695900293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19868122240645828927867057 14901091680484371695900293)
          ·
            refine ⟨2793954690090819692981305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14901091680484371695900293 2793954690090819692981305)
            ·
              refine ⟨2095466017568114769735979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2793954690090819692981305 2095466017568114769735979)
              ·
                refine ⟨3143199026352172154603969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2095466017568114769735979 3143199026352172154603969)
                ·
                  refine ⟨2357399269764129115952977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3143199026352172154603969 2357399269764129115952977)
                  ·
                    refine ⟨1768049452323096836964733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2357399269764129115952977 1768049452323096836964733)
                    ·
                      refine ⟨663018544621161313861775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1768049452323096836964733 663018544621161313861775)
                      ·
                        rfl

theorem cell23_1291224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_1291224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291224 prefixEnd_1291224 := by exact prefixLift 1291224
  have htrace : WordTrace (prefixWord ++ tailWord_1291224) baseStart_1291224 baseEnd_1291224 := by
    simpa [prefixWord, tailWord_1291224, baseEnd_1291224] using wordTrace_append hprefix tailTrace_1291224
  have hstable : (prefixWord ++ tailWord_1291224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291224).length < 2 ^ (prefixWord ++ tailWord_1291224).sum := by decide
  have hdescent : baseEnd_1291224 < baseStart_1291224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291280 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 5]
def baseStart_1291280 : Nat := 118140960795 + 1291280 * 2 ^ 59
def prefixEnd_1291280 : Nat := 4983230072969 + 3 ^ 40 * 1291280 * 2
def baseEnd_1291280 : Nat := 663047299537813094761517

theorem tailTrace_1291280 : CollatzResearch.WordTrace tailWord_1291280 prefixEnd_1291280 663047299537813094761517 := by
  unfold tailWord_1291280
  simp only [CollatzResearch.WordTrace]
  refine ⟨23548425380960283955787647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31397900507947045274383529 23548425380960283955787647)
  ·
    refine ⟨35322638071440425933681471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23548425380960283955787647 35322638071440425933681471)
    ·
      refine ⟨52983957107160638900522207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35322638071440425933681471 52983957107160638900522207)
      ·
        refine ⟨79475935660740958350783311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52983957107160638900522207 79475935660740958350783311)
        ·
          refine ⟨119213903491111437526174967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79475935660740958350783311 119213903491111437526174967)
          ·
            refine ⟨178820855236667156289262451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119213903491111437526174967 178820855236667156289262451)
            ·
              refine ⟨268231282855000734433893677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178820855236667156289262451 268231282855000734433893677)
              ·
                refine ⟨100586731070625275412710129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 268231282855000734433893677 100586731070625275412710129)
                ·
                  refine ⟨75440048302968956559532597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100586731070625275412710129 75440048302968956559532597)
                  ·
                    refine ⟨7072504528403339677456181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75440048302968956559532597 7072504528403339677456181)
                    ·
                      refine ⟨663047299537813094761517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7072504528403339677456181 663047299537813094761517)
                      ·
                        rfl

theorem cell23_1291280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 5].length) (baseStart_1291280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291280 prefixEnd_1291280 := by exact prefixLift 1291280
  have htrace : WordTrace (prefixWord ++ tailWord_1291280) baseStart_1291280 baseEnd_1291280 := by
    simpa [prefixWord, tailWord_1291280, baseEnd_1291280] using wordTrace_append hprefix tailTrace_1291280
  have hstable : (prefixWord ++ tailWord_1291280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291280).length < 2 ^ (prefixWord ++ tailWord_1291280).sum := by decide
  have hdescent : baseEnd_1291280 < baseStart_1291280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291282 : List Nat := [3, 2, 5, 1, 1, 1, 2, 3, 1, 4]
def baseStart_1291282 : Nat := 118140960795 + 1291282 * 2 ^ 59
def prefixEnd_1291282 : Nat := 4983230072969 + 3 ^ 40 * 1291282 * 2
def baseEnd_1291282 : Nat := 221016108833040695645503

theorem tailTrace_1291282 : CollatzResearch.WordTrace tailWord_1291282 prefixEnd_1291282 221016108833040695645503 := by
  unfold tailWord_1291282
  simp only [CollatzResearch.WordTrace]
  refine ⟨11774230926978330563287025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31397949138608881502098733 11774230926978330563287025)
  ·
    refine ⟨8830673195233747922465269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11774230926978330563287025 8830673195233747922465269)
    ·
      refine ⟨827875612053163867731119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8830673195233747922465269 827875612053163867731119)
      ·
        refine ⟨1241813418079745801596679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 827875612053163867731119 1241813418079745801596679)
        ·
          refine ⟨1862720127119618702395019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1241813418079745801596679 1862720127119618702395019)
          ·
            refine ⟨2794080190679428053592529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1862720127119618702395019 2794080190679428053592529)
            ·
              refine ⟨2095560143009571040194397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2794080190679428053592529 2095560143009571040194397)
              ·
                refine ⟨785835053628589140072899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2095560143009571040194397 785835053628589140072899)
                ·
                  refine ⟨1178752580442883710109349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 785835053628589140072899 1178752580442883710109349)
                  ·
                    refine ⟨221016108833040695645503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1178752580442883710109349 221016108833040695645503)
                    ·
                      rfl

theorem cell23_1291282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_1291282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291282 prefixEnd_1291282 := by exact prefixLift 1291282
  have htrace : WordTrace (prefixWord ++ tailWord_1291282) baseStart_1291282 baseEnd_1291282 := by
    simpa [prefixWord, tailWord_1291282, baseEnd_1291282] using wordTrace_append hprefix tailTrace_1291282
  have hstable : (prefixWord ++ tailWord_1291282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291282).length < 2 ^ (prefixWord ++ tailWord_1291282).sum := by decide
  have hdescent : baseEnd_1291282 < baseStart_1291282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291288 : List Nat := [2, 1, 2, 3, 2, 3, 2, 3, 1, 1, 3]
def baseStart_1291288 : Nat := 118140960795 + 1291288 * 2 ^ 59
def prefixEnd_1291288 : Nat := 4983230072969 + 3 ^ 40 * 1291288 * 2
def baseEnd_1291288 : Nat := 663051407383049063461481

theorem tailTrace_1291288 : CollatzResearch.WordTrace tailWord_1291288 prefixEnd_1291288 663051407383049063461481 := by
  unfold tailWord_1291288
  simp only [CollatzResearch.WordTrace]
  refine ⟨23548571272945792638933259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31398095030594390185244345 23548571272945792638933259)
  ·
    refine ⟨35322856909418688958399889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23548571272945792638933259 35322856909418688958399889)
    ·
      refine ⟨26492142682064016718799917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35322856909418688958399889 26492142682064016718799917)
      ·
        refine ⟨9934553505774006269549969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26492142682064016718799917 9934553505774006269549969)
        ·
          refine ⟨7450915129330504702162477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9934553505774006269549969 7450915129330504702162477)
          ·
            refine ⟨2794093173498939263310929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7450915129330504702162477 2794093173498939263310929)
            ·
              refine ⟨2095569880124204447483197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2794093173498939263310929 2095569880124204447483197)
              ·
                refine ⟨785838705046576667806199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2095569880124204447483197 785838705046576667806199)
                ·
                  refine ⟨1178758057569865001709299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 785838705046576667806199 1178758057569865001709299)
                  ·
                    refine ⟨1768137086354797502563949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1178758057569865001709299 1768137086354797502563949)
                    ·
                      refine ⟨663051407383049063461481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1768137086354797502563949 663051407383049063461481)
                      ·
                        rfl

theorem cell23_1291288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_1291288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291288 prefixEnd_1291288 := by exact prefixLift 1291288
  have htrace : WordTrace (prefixWord ++ tailWord_1291288) baseStart_1291288 baseEnd_1291288 := by
    simpa [prefixWord, tailWord_1291288, baseEnd_1291288] using wordTrace_append hprefix tailTrace_1291288
  have hstable : (prefixWord ++ tailWord_1291288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291288).length < 2 ^ (prefixWord ++ tailWord_1291288).sum := by decide
  have hdescent : baseEnd_1291288 < baseStart_1291288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291324 : List Nat := [2, 2, 2, 2, 2, 2, 3, 1, 1, 2, 4]
def baseStart_1291324 : Nat := 118140960795 + 1291324 * 2 ^ 59
def prefixEnd_1291324 : Nat := 4983230072969 + 3 ^ 40 * 1291324 * 2
def baseEnd_1291324 : Nat := 663069892686610922611315

theorem tailTrace_1291324 : CollatzResearch.WordTrace tailWord_1291324 prefixEnd_1291324 663069892686610922611315 := by
  unfold tailWord_1291324
  simp only [CollatzResearch.WordTrace]
  refine ⟨23549227786880581713088513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31398970382507442284118017 23549227786880581713088513)
  ·
    refine ⟨17661920840160436284816385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23549227786880581713088513 17661920840160436284816385)
    ·
      refine ⟨13246440630120327213612289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17661920840160436284816385 13246440630120327213612289)
      ·
        refine ⟨9934830472590245410209217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13246440630120327213612289 9934830472590245410209217)
        ·
          refine ⟨7451122854442684057656913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9934830472590245410209217 7451122854442684057656913)
          ·
            refine ⟨5588342140832013043242685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7451122854442684057656913 5588342140832013043242685)
            ·
              refine ⟨2095628302812004891216007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5588342140832013043242685 2095628302812004891216007)
              ·
                refine ⟨3143442454218007336824011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2095628302812004891216007 3143442454218007336824011)
                ·
                  refine ⟨4715163681327011005236017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3143442454218007336824011 4715163681327011005236017)
                  ·
                    refine ⟨3536372760995258253927013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4715163681327011005236017 3536372760995258253927013)
                    ·
                      refine ⟨663069892686610922611315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3536372760995258253927013 663069892686610922611315)
                      ·
                        rfl

theorem cell23_1291324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_1291324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291324 prefixEnd_1291324 := by exact prefixLift 1291324
  have htrace : WordTrace (prefixWord ++ tailWord_1291324) baseStart_1291324 baseEnd_1291324 := by
    simpa [prefixWord, tailWord_1291324, baseEnd_1291324] using wordTrace_append hprefix tailTrace_1291324
  have hstable : (prefixWord ++ tailWord_1291324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291324).length < 2 ^ (prefixWord ++ tailWord_1291324).sum := by decide
  have hdescent : baseEnd_1291324 < baseStart_1291324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291401 : List Nat := [1, 2, 1, 1, 4, 4, 1, 2, 1, 4, 2]
def baseStart_1291401 : Nat := 118140960795 + 1291401 * 2 ^ 59
def prefixEnd_1291401 : Nat := 4983230072969 + 3 ^ 40 * 1291401 * 2
def baseEnd_1291401 : Nat := 663109430697007121348461

theorem tailTrace_1291401 : CollatzResearch.WordTrace tailWord_1291401 prefixEnd_1291401 663109430697007121348461 := by
  unfold tailWord_1291401
  simp only [CollatzResearch.WordTrace]
  refine ⟨47101263994482205576730057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31400842662988137051153371 47101263994482205576730057)
  ·
    refine ⟨35325947995861654182547543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47101263994482205576730057 35325947995861654182547543)
    ·
      refine ⟨52988921993792481273821315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35325947995861654182547543 52988921993792481273821315)
      ·
        refine ⟨79483382990688721910731973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52988921993792481273821315 79483382990688721910731973)
        ·
          refine ⟨14903134310754135358262245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79483382990688721910731973 14903134310754135358262245)
          ·
            refine ⟨2794337683266400379674171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14903134310754135358262245 2794337683266400379674171)
            ·
              refine ⟨4191506524899600569511257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2794337683266400379674171 4191506524899600569511257)
              ·
                refine ⟨3143629893674700427133443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4191506524899600569511257 3143629893674700427133443)
                ·
                  refine ⟨4715444840512050640700165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3143629893674700427133443 4715444840512050640700165)
                  ·
                    refine ⟨884145907596009495131281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4715444840512050640700165 884145907596009495131281)
                    ·
                      refine ⟨663109430697007121348461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 884145907596009495131281 663109430697007121348461)
                      ·
                        rfl

theorem cell23_1291401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 4, 2].length) (baseStart_1291401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291401 prefixEnd_1291401 := by exact prefixLift 1291401
  have htrace : WordTrace (prefixWord ++ tailWord_1291401) baseStart_1291401 baseEnd_1291401 := by
    simpa [prefixWord, tailWord_1291401, baseEnd_1291401] using wordTrace_append hprefix tailTrace_1291401
  have hstable : (prefixWord ++ tailWord_1291401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291401).length < 2 ^ (prefixWord ++ tailWord_1291401).sum := by decide
  have hdescent : baseEnd_1291401 < baseStart_1291401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291431 : List Nat := [1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_1291431 : Nat := 118140960795 + 1291431 * 2 ^ 59
def prefixEnd_1291431 : Nat := 4983230072969 + 3 ^ 40 * 1291431 * 2
def baseEnd_1291431 : Nat := 663124835116642003973323

theorem tailTrace_1291431 : CollatzResearch.WordTrace tailWord_1291431 prefixEnd_1291431 663124835116642003973323 := by
  unfold tailWord_1291431
  simp only [CollatzResearch.WordTrace]
  refine ⟨47102358184373520700322147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31401572122915680466881431 47102358184373520700322147)
  ·
    refine ⟨70653537276560281050483221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47102358184373520700322147 70653537276560281050483221)
    ·
      refine ⟨3311884559838763174241401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 70653537276560281050483221 3311884559838763174241401)
      ·
        refine ⟨2483913419879072380681051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3311884559838763174241401 2483913419879072380681051)
        ·
          refine ⟨3725870129818608571021577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2483913419879072380681051 3725870129818608571021577)
          ·
            refine ⟨2794402597363956428266183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3725870129818608571021577 2794402597363956428266183)
            ·
              refine ⟨4191603896045934642399275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2794402597363956428266183 4191603896045934642399275)
              ·
                refine ⟨6287405844068901963598913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4191603896045934642399275 6287405844068901963598913)
                ·
                  refine ⟨4715554383051676472699185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6287405844068901963598913 4715554383051676472699185)
                  ·
                    refine ⟨3536665787288757354524389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4715554383051676472699185 3536665787288757354524389)
                    ·
                      refine ⟨663124835116642003973323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3536665787288757354524389 663124835116642003973323)
                      ·
                        rfl

theorem cell23_1291431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_1291431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291431 prefixEnd_1291431 := by exact prefixLift 1291431
  have htrace : WordTrace (prefixWord ++ tailWord_1291431) baseStart_1291431 baseEnd_1291431 := by
    simpa [prefixWord, tailWord_1291431, baseEnd_1291431] using wordTrace_append hprefix tailTrace_1291431
  have hstable : (prefixWord ++ tailWord_1291431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291431).length < 2 ^ (prefixWord ++ tailWord_1291431).sum := by decide
  have hdescent : baseEnd_1291431 < baseStart_1291431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291497 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 12]
def baseStart_1291497 : Nat := 118140960795 + 1291497 * 2 ^ 59
def prefixEnd_1291497 : Nat := 4983230072969 + 3 ^ 40 * 1291497 * 2
def baseEnd_1291497 : Nat := 73684302759982082860891

theorem tailTrace_1291497 : CollatzResearch.WordTrace tailWord_1291497 prefixEnd_1291497 73684302759982082860891 := by
  unfold tailWord_1291497
  simp only [CollatzResearch.WordTrace]
  refine ⟨47104765402134413972224745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31403176934756275981483163 47104765402134413972224745)
  ·
    refine ⟨35328574051600810479168559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47104765402134413972224745 35328574051600810479168559)
    ·
      refine ⟨52992861077401215718752839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35328574051600810479168559 52992861077401215718752839)
      ·
        refine ⟨79489291616101823578129259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52992861077401215718752839 79489291616101823578129259)
        ·
          refine ⟨119233937424152735367193889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79489291616101823578129259 119233937424152735367193889)
          ·
            refine ⟨89425453068114551525395417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119233937424152735367193889 89425453068114551525395417)
            ·
              refine ⟨67069089801085913644046563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89425453068114551525395417 67069089801085913644046563)
              ·
                refine ⟨100603634701628870466069845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67069089801085913644046563 100603634701628870466069845)
                ·
                  refine ⟨73684302759982082860891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 100603634701628870466069845 73684302759982082860891)
                  ·
                    rfl

theorem cell23_1291497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 12].length) (baseStart_1291497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291497 prefixEnd_1291497 := by exact prefixLift 1291497
  have htrace : WordTrace (prefixWord ++ tailWord_1291497) baseStart_1291497 baseEnd_1291497 := by
    simpa [prefixWord, tailWord_1291497, baseEnd_1291497] using wordTrace_append hprefix tailTrace_1291497
  have hstable : (prefixWord ++ tailWord_1291497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291497).length < 2 ^ (prefixWord ++ tailWord_1291497).sum := by decide
  have hdescent : baseEnd_1291497 < baseStart_1291497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291528 : List Nat := [2, 1, 3, 2, 4, 1, 1, 2, 2, 2, 3]
def baseStart_1291528 : Nat := 118140960795 + 1291528 * 2 ^ 59
def prefixEnd_1291528 : Nat := 4983230072969 + 3 ^ 40 * 1291528 * 2
def baseEnd_1291528 : Nat := 663174642740128124460377

theorem tailTrace_1291528 : CollatzResearch.WordTrace tailWord_1291528 prefixEnd_1291528 663174642740128124460377 := by
  unfold tailWord_1291528
  simp only [CollatzResearch.WordTrace]
  refine ⟨23552948032511053133301619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31403930710014737511068825 23552948032511053133301619)
  ·
    refine ⟨35329422048766579699952429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23552948032511053133301619 35329422048766579699952429)
    ·
      refine ⟨13248533268287467387482161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35329422048766579699952429 13248533268287467387482161)
      ·
        refine ⟨9936399951215600540611621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13248533268287467387482161 9936399951215600540611621)
        ·
          refine ⟨1863074990852925101364679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9936399951215600540611621 1863074990852925101364679)
          ·
            refine ⟨2794612486279387652047019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1863074990852925101364679 2794612486279387652047019)
            ·
              refine ⟨4191918729419081478070529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2794612486279387652047019 4191918729419081478070529)
              ·
                refine ⟨3143939047064311108552897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4191918729419081478070529 3143939047064311108552897)
                ·
                  refine ⟨2357954285298233331414673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3143939047064311108552897 2357954285298233331414673)
                  ·
                    refine ⟨1768465713973674998561005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2357954285298233331414673 1768465713973674998561005)
                    ·
                      refine ⟨663174642740128124460377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1768465713973674998561005 663174642740128124460377)
                      ·
                        rfl

theorem cell23_1291528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_1291528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291528 prefixEnd_1291528 := by exact prefixLift 1291528
  have htrace : WordTrace (prefixWord ++ tailWord_1291528) baseStart_1291528 baseEnd_1291528 := by
    simpa [prefixWord, tailWord_1291528, baseEnd_1291528] using wordTrace_append hprefix tailTrace_1291528
  have hstable : (prefixWord ++ tailWord_1291528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291528).length < 2 ^ (prefixWord ++ tailWord_1291528).sum := by decide
  have hdescent : baseEnd_1291528 < baseStart_1291528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291568 : List Nat := [2, 1, 1, 1, 2, 2, 6, 1, 2, 3, 2]
def baseStart_1291568 : Nat := 118140960795 + 1291568 * 2 ^ 59
def prefixEnd_1291568 : Nat := 4983230072969 + 3 ^ 40 * 1291568 * 2
def baseEnd_1291568 : Nat := 663195181966307967960193

theorem tailTrace_1291568 : CollatzResearch.WordTrace tailWord_1291568 prefixEnd_1291568 663195181966307967960193 := by
  unfold tailWord_1291568
  simp only [CollatzResearch.WordTrace]
  refine ⟨23553677492438596549029679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31404903323251462065372905 23553677492438596549029679)
  ·
    refine ⟨35330516238657894823544519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23553677492438596549029679 35330516238657894823544519)
    ·
      refine ⟨52995774357986842235316779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35330516238657894823544519 52995774357986842235316779)
      ·
        refine ⟨79493661536980263352975169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52995774357986842235316779 79493661536980263352975169)
        ·
          refine ⟨59620246152735197514731377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79493661536980263352975169 59620246152735197514731377)
          ·
            refine ⟨44715184614551398136048533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59620246152735197514731377 44715184614551398136048533)
            ·
              refine ⟨2096024278807096787627275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44715184614551398136048533 2096024278807096787627275)
              ·
                refine ⟨3144036418210645181440913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2096024278807096787627275 3144036418210645181440913)
                ·
                  refine ⟨2358027313657983886080685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3144036418210645181440913 2358027313657983886080685)
                  ·
                    refine ⟨884260242621743957280257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2358027313657983886080685 884260242621743957280257)
                    ·
                      refine ⟨663195181966307967960193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 884260242621743957280257 663195181966307967960193)
                      ·
                        rfl

theorem cell23_1291568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 2, 3, 2].length) (baseStart_1291568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291568 prefixEnd_1291568 := by exact prefixLift 1291568
  have htrace : WordTrace (prefixWord ++ tailWord_1291568) baseStart_1291568 baseEnd_1291568 := by
    simpa [prefixWord, tailWord_1291568, baseEnd_1291568] using wordTrace_append hprefix tailTrace_1291568
  have hstable : (prefixWord ++ tailWord_1291568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291568).length < 2 ^ (prefixWord ++ tailWord_1291568).sum := by decide
  have hdescent : baseEnd_1291568 < baseStart_1291568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291578 : List Nat := [3, 1, 1, 1, 4, 1, 5, 1, 1, 5]
def baseStart_1291578 : Nat := 118140960795 + 1291578 * 2 ^ 59
def prefixEnd_1291578 : Nat := 4983230072969 + 3 ^ 40 * 1291578 * 2
def baseEnd_1291578 : Nat := 221066772257617642945049

theorem tailTrace_1291578 : CollatzResearch.WordTrace tailWord_1291578 prefixEnd_1291578 221066772257617642945049 := by
  unfold tailWord_1291578
  simp only [CollatzResearch.WordTrace]
  refine ⟨11776929928710241201480847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31405146476560643203948925 11776929928710241201480847)
  ·
    refine ⟨17665394893065361802221271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11776929928710241201480847 17665394893065361802221271)
    ·
      refine ⟨26498092339598042703331907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17665394893065361802221271 26498092339598042703331907)
      ·
        refine ⟨39747138509397064054997861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26498092339598042703331907 39747138509397064054997861)
        ·
          refine ⟨7452588470511949510312099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39747138509397064054997861 7452588470511949510312099)
          ·
            refine ⟨11178882705767924265468149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7452588470511949510312099 11178882705767924265468149)
            ·
              refine ⟨1048020253665742899887639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11178882705767924265468149 1048020253665742899887639)
              ·
                refine ⟨1572030380498614349831459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1048020253665742899887639 1572030380498614349831459)
                ·
                  refine ⟨2358045570747921524747189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1572030380498614349831459 2358045570747921524747189)
                  ·
                    refine ⟨221066772257617642945049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2358045570747921524747189 221066772257617642945049)
                    ·
                      rfl

theorem cell23_1291578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 1, 5].length) (baseStart_1291578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291578 prefixEnd_1291578 := by exact prefixLift 1291578
  have htrace : WordTrace (prefixWord ++ tailWord_1291578) baseStart_1291578 baseEnd_1291578 := by
    simpa [prefixWord, tailWord_1291578, baseEnd_1291578] using wordTrace_append hprefix tailTrace_1291578
  have hstable : (prefixWord ++ tailWord_1291578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291578).length < 2 ^ (prefixWord ++ tailWord_1291578).sum := by decide
  have hdescent : baseEnd_1291578 < baseStart_1291578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291585 : List Nat := [1, 2, 5, 2, 1, 1, 2, 2, 2, 3, 2]
def baseStart_1291585 : Nat := 118140960795 + 1291585 * 2 ^ 59
def prefixEnd_1291585 : Nat := 4983230072969 + 3 ^ 40 * 1291585 * 2
def baseEnd_1291585 : Nat := 663203911137434401447615

theorem tailTrace_1291585 : CollatzResearch.WordTrace tailWord_1291585 prefixEnd_1291585 663203911137434401447615 := by
  unfold tailWord_1291585
  simp only [CollatzResearch.WordTrace]
  refine ⟨47107975025815605001428209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31405316683877070000952139 47107975025815605001428209)
  ·
    refine ⟨35330981269361703751071157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47107975025815605001428209 35330981269361703751071157)
    ·
      refine ⟨3312279494002659726662921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35330981269361703751071157 3312279494002659726662921)
      ·
        refine ⟨2484209620501994794997191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3312279494002659726662921 2484209620501994794997191)
        ·
          refine ⟨3726314430752992192495787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2484209620501994794997191 3726314430752992192495787)
          ·
            refine ⟨5589471646129488288743681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3726314430752992192495787 5589471646129488288743681)
            ·
              refine ⟨4192103734597116216557761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5589471646129488288743681 4192103734597116216557761)
              ·
                refine ⟨3144077800947837162418321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4192103734597116216557761 3144077800947837162418321)
                ·
                  refine ⟨2358058350710877871813741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3144077800947837162418321 2358058350710877871813741)
                  ·
                    refine ⟨884271881516579201930153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2358058350710877871813741 884271881516579201930153)
                    ·
                      refine ⟨663203911137434401447615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 884271881516579201930153 663203911137434401447615)
                      ·
                        rfl

theorem cell23_1291585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_1291585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291585 prefixEnd_1291585 := by exact prefixLift 1291585
  have htrace : WordTrace (prefixWord ++ tailWord_1291585) baseStart_1291585 baseEnd_1291585 := by
    simpa [prefixWord, tailWord_1291585, baseEnd_1291585] using wordTrace_append hprefix tailTrace_1291585
  have hstable : (prefixWord ++ tailWord_1291585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291585).length < 2 ^ (prefixWord ++ tailWord_1291585).sum := by decide
  have hdescent : baseEnd_1291585 < baseStart_1291585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291594 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 3, 1, 6]
def baseStart_1291594 : Nat := 118140960795 + 1291594 * 2 ^ 59
def prefixEnd_1291594 : Nat := 4983230072969 + 3 ^ 40 * 1291594 * 2
def baseEnd_1291594 : Nat := 663208532463324866235073

theorem tailTrace_1291594 : CollatzResearch.WordTrace tailWord_1291594 prefixEnd_1291594 663208532463324866235073 := by
  unfold tailWord_1291594
  simp only [CollatzResearch.WordTrace]
  refine ⟨11777075820695749884626459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31405535521855333025670557 11777075820695749884626459)
  ·
    refine ⟨17665613731043624826939689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11777075820695749884626459 17665613731043624826939689)
    ·
      refine ⟨13249210298282718620204767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17665613731043624826939689 13249210298282718620204767)
      ·
        refine ⟨19873815447424077930307151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13249210298282718620204767 19873815447424077930307151)
        ·
          refine ⟨29810723171136116895460727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19873815447424077930307151 29810723171136116895460727)
          ·
            refine ⟨44716084756704175343191091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29810723171136116895460727 44716084756704175343191091)
            ·
              refine ⟨67074127135056263014786637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44716084756704175343191091 67074127135056263014786637)
              ·
                refine ⟨25152797675646098630544989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67074127135056263014786637 25152797675646098630544989)
                ·
                  refine ⟨9432299128367286986454371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25152797675646098630544989 9432299128367286986454371)
                  ·
                    refine ⟨14148448692550930479681557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9432299128367286986454371 14148448692550930479681557)
                    ·
                      refine ⟨663208532463324866235073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14148448692550930479681557 663208532463324866235073)
                      ·
                        rfl

theorem cell23_1291594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_1291594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291594 prefixEnd_1291594 := by exact prefixLift 1291594
  have htrace : WordTrace (prefixWord ++ tailWord_1291594) baseStart_1291594 baseEnd_1291594 := by
    simpa [prefixWord, tailWord_1291594, baseEnd_1291594] using wordTrace_append hprefix tailTrace_1291594
  have hstable : (prefixWord ++ tailWord_1291594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291594).length < 2 ^ (prefixWord ++ tailWord_1291594).sum := by decide
  have hdescent : baseEnd_1291594 < baseStart_1291594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291601 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 5, 2, 3]
def baseStart_1291601 : Nat := 118140960795 + 1291601 * 2 ^ 59
def prefixEnd_1291601 : Nat := 4983230072969 + 3 ^ 40 * 1291601 * 2
def baseEnd_1291601 : Nat := 663212126827906338847541

theorem tailTrace_1291601 : CollatzResearch.WordTrace tailWord_1291601 prefixEnd_1291601 663212126827906338847541 := by
  unfold tailWord_1291601
  simp only [CollatzResearch.WordTrace]
  refine ⟨47108558593757639734010657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31405705729171759822673771 47108558593757639734010657)
  ·
    refine ⟨35331418945318229800507993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47108558593757639734010657 35331418945318229800507993)
    ·
      refine ⟨26498564208988672350380995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35331418945318229800507993 26498564208988672350380995)
      ·
        refine ⟨39747846313483008525571493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26498564208988672350380995 39747846313483008525571493)
        ·
          refine ⟨7452721183778064098544655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39747846313483008525571493 7452721183778064098544655)
          ·
            refine ⟨11179081775667096147816983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7452721183778064098544655 11179081775667096147816983)
            ·
              refine ⟨16768622663500644221725475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11179081775667096147816983 16768622663500644221725475)
              ·
                refine ⟨25152933995250966332588213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16768622663500644221725475 25152933995250966332588213)
                ·
                  refine ⟨2358087562054778093680145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25152933995250966332588213 2358087562054778093680145)
                  ·
                    refine ⟨1768565671541083570260109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2358087562054778093680145 1768565671541083570260109)
                    ·
                      refine ⟨663212126827906338847541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1768565671541083570260109 663212126827906338847541)
                      ·
                        rfl

theorem cell23_1291601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 2, 3].length) (baseStart_1291601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291601 prefixEnd_1291601 := by exact prefixLift 1291601
  have htrace : WordTrace (prefixWord ++ tailWord_1291601) baseStart_1291601 baseEnd_1291601 := by
    simpa [prefixWord, tailWord_1291601, baseEnd_1291601] using wordTrace_append hprefix tailTrace_1291601
  have hstable : (prefixWord ++ tailWord_1291601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291601).length < 2 ^ (prefixWord ++ tailWord_1291601).sum := by decide
  have hdescent : baseEnd_1291601 < baseStart_1291601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291618 : List Nat := [3, 3, 2, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_1291618 : Nat := 118140960795 + 1291618 * 2 ^ 59
def prefixEnd_1291618 : Nat := 4983230072969 + 3 ^ 40 * 1291618 * 2
def baseEnd_1291618 : Nat := 663220855999032772334963

theorem tailTrace_1291618 : CollatzResearch.WordTrace tailWord_1291618 prefixEnd_1291618 663220855999032772334963 := by
  unfold tailWord_1291618
  simp only [CollatzResearch.WordTrace]
  refine ⟨11777294658674012909344877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31406119089797367758253005 11777294658674012909344877)
  ·
    refine ⟨4416485497002754841004329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11777294658674012909344877 4416485497002754841004329)
    ·
      refine ⟨3312364122752066130753247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4416485497002754841004329 3312364122752066130753247)
      ·
        refine ⟨4968546184128099196129871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3312364122752066130753247 4968546184128099196129871)
        ·
          refine ⟨7452819276192148794194807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4968546184128099196129871 7452819276192148794194807)
          ·
            refine ⟨11179228914288223191292211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7452819276192148794194807 11179228914288223191292211)
            ·
              refine ⟨16768843371432334786938317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11179228914288223191292211 16768843371432334786938317)
              ·
                refine ⟨6288316264287125545101869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16768843371432334786938317 6288316264287125545101869)
                ·
                  refine ⟨2358118599107672079413201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6288316264287125545101869 2358118599107672079413201)
                  ·
                    refine ⟨1768588949330754059559901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2358118599107672079413201 1768588949330754059559901)
                    ·
                      refine ⟨663220855999032772334963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1768588949330754059559901 663220855999032772334963)
                      ·
                        rfl

theorem cell23_1291618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_1291618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291618 prefixEnd_1291618 := by exact prefixLift 1291618
  have htrace : WordTrace (prefixWord ++ tailWord_1291618) baseStart_1291618 baseEnd_1291618 := by
    simpa [prefixWord, tailWord_1291618, baseEnd_1291618] using wordTrace_append hprefix tailTrace_1291618
  have hstable : (prefixWord ++ tailWord_1291618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291618).length < 2 ^ (prefixWord ++ tailWord_1291618).sum := by decide
  have hdescent : baseEnd_1291618 < baseStart_1291618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291621 : List Nat := [1, 3, 1, 3, 1, 2, 5, 7]
def baseStart_1291621 : Nat := 118140960795 + 1291621 * 2 ^ 59
def prefixEnd_1291621 : Nat := 4983230072969 + 3 ^ 40 * 1291621 * 2
def baseEnd_1291621 : Nat := 24563792460777639281387

theorem tailTrace_1291621 : CollatzResearch.WordTrace tailWord_1291621 prefixEnd_1291621 24563792460777639281387 := by
  unfold tailWord_1291621
  simp only [CollatzResearch.WordTrace]
  refine ⟨47109288053685183149738717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31406192035790122099825811 47109288053685183149738717)
  ·
    refine ⟨17665983020131943681152019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47109288053685183149738717 17665983020131943681152019)
    ·
      refine ⟨26498974530197915521728029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17665983020131943681152019 26498974530197915521728029)
      ·
        refine ⟨9937115448824218320648011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26498974530197915521728029 9937115448824218320648011)
        ·
          refine ⟨14905673173236327480972017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9937115448824218320648011 14905673173236327480972017)
          ·
            refine ⟨11179254879927245610729013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14905673173236327480972017 11179254879927245610729013)
            ·
              refine ⟨1048055144993179276005845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11179254879927245610729013 1048055144993179276005845)
              ·
                refine ⟨24563792460777639281387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1048055144993179276005845 24563792460777639281387)
                ·
                  rfl

theorem cell23_1291621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 7].length) (baseStart_1291621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291621 prefixEnd_1291621 := by exact prefixLift 1291621
  have htrace : WordTrace (prefixWord ++ tailWord_1291621) baseStart_1291621 baseEnd_1291621 := by
    simpa [prefixWord, tailWord_1291621, baseEnd_1291621] using wordTrace_append hprefix tailTrace_1291621
  have hstable : (prefixWord ++ tailWord_1291621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291621).length < 2 ^ (prefixWord ++ tailWord_1291621).sum := by decide
  have hdescent : baseEnd_1291621 < baseStart_1291621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291631 : List Nat := [1, 1, 2, 1, 3, 1, 3, 4, 1, 3, 3]
def baseStart_1291631 : Nat := 118140960795 + 1291631 * 2 ^ 59
def prefixEnd_1291631 : Nat := 4983230072969 + 3 ^ 40 * 1291631 * 2
def baseEnd_1291631 : Nat := 663227531247541221472403

theorem tailTrace_1291631 : CollatzResearch.WordTrace tailWord_1291631 prefixEnd_1291631 663227531247541221472403 := by
  unfold tailWord_1291631
  simp only [CollatzResearch.WordTrace]
  refine ⟨47109652783648954857602747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31406435189099303238401831 47109652783648954857602747)
  ·
    refine ⟨70664479175473432286404121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47109652783648954857602747 70664479175473432286404121)
    ·
      refine ⟨52998359381605074214803091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70664479175473432286404121 52998359381605074214803091)
      ·
        refine ⟨79497539072407611322204637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52998359381605074214803091 79497539072407611322204637)
        ·
          refine ⟨29811577152152854245826739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79497539072407611322204637 29811577152152854245826739)
          ·
            refine ⟨44717365728229281368740109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29811577152152854245826739 44717365728229281368740109)
            ·
              refine ⟨16769012148085980513277541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44717365728229281368740109 16769012148085980513277541)
              ·
                refine ⟨3144189777766121346239539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16769012148085980513277541 3144189777766121346239539)
                ·
                  refine ⟨4716284666649182019359309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3144189777766121346239539 4716284666649182019359309)
                  ·
                    refine ⟨1768606749993443257259741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4716284666649182019359309 1768606749993443257259741)
                    ·
                      refine ⟨663227531247541221472403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1768606749993443257259741 663227531247541221472403)
                      ·
                        rfl

theorem cell23_1291631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3, 3].length) (baseStart_1291631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291631 prefixEnd_1291631 := by exact prefixLift 1291631
  have htrace : WordTrace (prefixWord ++ tailWord_1291631) baseStart_1291631 baseEnd_1291631 := by
    simpa [prefixWord, tailWord_1291631, baseEnd_1291631] using wordTrace_append hprefix tailTrace_1291631
  have hstable : (prefixWord ++ tailWord_1291631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291631).length < 2 ^ (prefixWord ++ tailWord_1291631).sum := by decide
  have hdescent : baseEnd_1291631 < baseStart_1291631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291632 : List Nat := [2, 1, 1, 1, 4, 2, 4, 3, 1, 2, 2]
def baseStart_1291632 : Nat := 118140960795 + 1291632 * 2 ^ 59
def prefixEnd_1291632 : Nat := 4983230072969 + 3 ^ 40 * 1291632 * 2
def baseEnd_1291632 : Nat := 663228044728195717559899

theorem tailTrace_1291632 : CollatzResearch.WordTrace tailWord_1291632 prefixEnd_1291632 663228044728195717559899 := by
  unfold tailWord_1291632
  simp only [CollatzResearch.WordTrace]
  refine ⟨23554844628322666014194575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31406459504430221352259433 23554844628322666014194575)
  ·
    refine ⟨35332266942483999021291863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23554844628322666014194575 35332266942483999021291863)
    ·
      refine ⟨52998400413725998531937795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35332266942483999021291863 52998400413725998531937795)
      ·
        refine ⟨79497600620588997797906693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52998400413725998531937795 79497600620588997797906693)
        ·
          refine ⟨14905800116360437087107505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79497600620588997797906693 14905800116360437087107505)
          ·
            refine ⟨11179350087270327815330629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14905800116360437087107505 11179350087270327815330629)
            ·
              refine ⟨2096128141363186465374493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11179350087270327815330629 2096128141363186465374493)
              ·
                refine ⟨786048053011194924515435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2096128141363186465374493 786048053011194924515435)
                ·
                  refine ⟨1179072079516792386773153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 786048053011194924515435 1179072079516792386773153)
                  ·
                    refine ⟨884304059637594290079865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1179072079516792386773153 884304059637594290079865)
                    ·
                      refine ⟨663228044728195717559899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 884304059637594290079865 663228044728195717559899)
                      ·
                        rfl

theorem cell23_1291632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3, 1, 2, 2].length) (baseStart_1291632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291632 prefixEnd_1291632 := by exact prefixLift 1291632
  have htrace : WordTrace (prefixWord ++ tailWord_1291632) baseStart_1291632 baseEnd_1291632 := by
    simpa [prefixWord, tailWord_1291632, baseEnd_1291632] using wordTrace_append hprefix tailTrace_1291632
  have hstable : (prefixWord ++ tailWord_1291632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291632).length < 2 ^ (prefixWord ++ tailWord_1291632).sum := by decide
  have hdescent : baseEnd_1291632 < baseStart_1291632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291662 : List Nat := [4, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4]
def baseStart_1291662 : Nat := 118140960795 + 1291662 * 2 ^ 59
def prefixEnd_1291662 : Nat := 4983230072969 + 3 ^ 40 * 1291662 * 2
def baseEnd_1291662 : Nat := 663243449147830600184761

theorem tailTrace_1291662 : CollatzResearch.WordTrace tailWord_1291662 prefixEnd_1291662 663243449147830600184761 := by
  unfold tailWord_1291662
  simp only [CollatzResearch.WordTrace]
  refine ⟨5888847930817080893997655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31407188964357764767987493 5888847930817080893997655)
  ·
    refine ⟨8833271896225621340996483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5888847930817080893997655 8833271896225621340996483)
    ·
      refine ⟨13249907844338432011494725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8833271896225621340996483 13249907844338432011494725)
      ·
        refine ⟨2484357720813456002155261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13249907844338432011494725 2484357720813456002155261)
        ·
          refine ⟨931634145305046000808223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2484357720813456002155261 931634145305046000808223)
          ·
            refine ⟨1397451217957569001212335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 931634145305046000808223 1397451217957569001212335)
            ·
              refine ⟨2096176826936353501818503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1397451217957569001212335 2096176826936353501818503)
              ·
                refine ⟨3144265240404530252727755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2096176826936353501818503 3144265240404530252727755)
                ·
                  refine ⟨4716397860606795379091633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3144265240404530252727755 4716397860606795379091633)
                  ·
                    refine ⟨3537298395455096534318725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4716397860606795379091633 3537298395455096534318725)
                    ·
                      refine ⟨663243449147830600184761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3537298395455096534318725 663243449147830600184761)
                      ·
                        rfl

theorem cell23_1291662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_1291662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291662 prefixEnd_1291662 := by exact prefixLift 1291662
  have htrace : WordTrace (prefixWord ++ tailWord_1291662) baseStart_1291662 baseEnd_1291662 := by
    simpa [prefixWord, tailWord_1291662, baseEnd_1291662] using wordTrace_append hprefix tailTrace_1291662
  have hstable : (prefixWord ++ tailWord_1291662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291662).length < 2 ^ (prefixWord ++ tailWord_1291662).sum := by decide
  have hdescent : baseEnd_1291662 < baseStart_1291662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291721 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 1, 5, 3]
def baseStart_1291721 : Nat := 118140960795 + 1291721 * 2 ^ 59
def prefixEnd_1291721 : Nat := 4983230072969 + 3 ^ 40 * 1291721 * 2
def baseEnd_1291721 : Nat := 663273744506445869346989

theorem tailTrace_1291721 : CollatzResearch.WordTrace tailWord_1291721 prefixEnd_1291721 663273744506445869346989 := by
  unfold tailWord_1291721
  simp only [CollatzResearch.WordTrace]
  refine ⟨47112935353322900228379017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31408623568881933485586011 47112935353322900228379017)
  ·
    refine ⟨35334701514992175171284263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47112935353322900228379017 35334701514992175171284263)
    ·
      refine ⟨53002052272488262756926395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35334701514992175171284263 53002052272488262756926395)
      ·
        refine ⟨79503078408732394135389593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53002052272488262756926395 79503078408732394135389593)
        ·
          refine ⟨59627308806549295601542195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79503078408732394135389593 59627308806549295601542195)
          ·
            refine ⟨89440963209823943402313293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59627308806549295601542195 89440963209823943402313293)
            ·
              refine ⟨33540361203683978775867485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89440963209823943402313293 33540361203683978775867485)
              ·
                refine ⟨12577635451381492040950307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33540361203683978775867485 12577635451381492040950307)
                ·
                  refine ⟨18866453177072238061425461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12577635451381492040950307 18866453177072238061425461)
                  ·
                    refine ⟨1768729985350522318258637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18866453177072238061425461 1768729985350522318258637)
                    ·
                      refine ⟨663273744506445869346989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1768729985350522318258637 663273744506445869346989)
                      ·
                        rfl

theorem cell23_1291721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 5, 3].length) (baseStart_1291721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291721 prefixEnd_1291721 := by exact prefixLift 1291721
  have htrace : WordTrace (prefixWord ++ tailWord_1291721) baseStart_1291721 baseEnd_1291721 := by
    simpa [prefixWord, tailWord_1291721, baseEnd_1291721] using wordTrace_append hprefix tailTrace_1291721
  have hstable : (prefixWord ++ tailWord_1291721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291721).length < 2 ^ (prefixWord ++ tailWord_1291721).sum := by decide
  have hdescent : baseEnd_1291721 < baseStart_1291721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291722 : List Nat := [3, 1, 2, 1, 2, 4, 1, 3, 2, 2, 2]
def baseStart_1291722 : Nat := 118140960795 + 1291722 * 2 ^ 59
def prefixEnd_1291722 : Nat := 4983230072969 + 3 ^ 40 * 1291722 * 2
def baseEnd_1291722 : Nat := 663274257987100365434485

theorem tailTrace_1291722 : CollatzResearch.WordTrace tailWord_1291722 prefixEnd_1291722 663274257987100365434485 := by
  unfold tailWord_1291722
  simp only [CollatzResearch.WordTrace]
  refine ⟨11778242956579819349791355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31408647884212851599443613 11778242956579819349791355)
  ·
    refine ⟨17667364434869729024687033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11778242956579819349791355 17667364434869729024687033)
    ·
      refine ⟨13250523326152296768515275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17667364434869729024687033 13250523326152296768515275)
      ·
        refine ⟨19875784989228445152772913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13250523326152296768515275 19875784989228445152772913)
        ·
          refine ⟨14906838741921333864579685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19875784989228445152772913 14906838741921333864579685)
          ·
            refine ⟨2795032264110250099608691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14906838741921333864579685 2795032264110250099608691)
            ·
              refine ⟨4192548396165375149413037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2795032264110250099608691 4192548396165375149413037)
              ·
                refine ⟨1572205648562015681029889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4192548396165375149413037 1572205648562015681029889)
                ·
                  refine ⟨1179154236421511760772417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1572205648562015681029889 1179154236421511760772417)
                  ·
                    refine ⟨884365677316133820579313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1179154236421511760772417 884365677316133820579313)
                    ·
                      refine ⟨663274257987100365434485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 884365677316133820579313 663274257987100365434485)
                      ·
                        rfl

theorem cell23_1291722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 2, 2, 2].length) (baseStart_1291722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291722 prefixEnd_1291722 := by exact prefixLift 1291722
  have htrace : WordTrace (prefixWord ++ tailWord_1291722) baseStart_1291722 baseEnd_1291722 := by
    simpa [prefixWord, tailWord_1291722, baseEnd_1291722] using wordTrace_append hprefix tailTrace_1291722
  have hstable : (prefixWord ++ tailWord_1291722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291722).length < 2 ^ (prefixWord ++ tailWord_1291722).sum := by decide
  have hdescent : baseEnd_1291722 < baseStart_1291722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291748 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 4, 5, 2]
def baseStart_1291748 : Nat := 118140960795 + 1291748 * 2 ^ 59
def prefixEnd_1291748 : Nat := 4983230072969 + 3 ^ 40 * 1291748 * 2
def baseEnd_1291748 : Nat := 663287608484117263709365

theorem tailTrace_1291748 : CollatzResearch.WordTrace tailWord_1291748 prefixEnd_1291748 663287608484117263709365 := by
  unfold tailWord_1291748
  simp only [CollatzResearch.WordTrace]
  refine ⟨23556960062112541919805949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31409280082816722559741265 23556960062112541919805949)
  ·
    refine ⟨8833860023292203219927231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23556960062112541919805949 8833860023292203219927231)
    ·
      refine ⟨13250790034938304829890847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8833860023292203219927231 13250790034938304829890847)
      ·
        refine ⟨19876185052407457244836271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13250790034938304829890847 19876185052407457244836271)
        ·
          refine ⟨29814277578611185867254407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19876185052407457244836271 29814277578611185867254407)
          ·
            refine ⟨44721416367916778800881611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29814277578611185867254407 44721416367916778800881611)
            ·
              refine ⟨67082124551875168201322417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44721416367916778800881611 67082124551875168201322417)
              ·
                refine ⟨50311593413906376150991813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67082124551875168201322417 50311593413906376150991813)
                ·
                  refine ⟨9433423765107445528310965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50311593413906376150991813 9433423765107445528310965)
                  ·
                    refine ⟨884383477978823018279153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9433423765107445528310965 884383477978823018279153)
                    ·
                      refine ⟨663287608484117263709365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 884383477978823018279153 663287608484117263709365)
                      ·
                        rfl

theorem cell23_1291748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 4, 5, 2].length) (baseStart_1291748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291748 prefixEnd_1291748 := by exact prefixLift 1291748
  have htrace : WordTrace (prefixWord ++ tailWord_1291748) baseStart_1291748 baseEnd_1291748 := by
    simpa [prefixWord, tailWord_1291748, baseEnd_1291748] using wordTrace_append hprefix tailTrace_1291748
  have hstable : (prefixWord ++ tailWord_1291748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291748).length < 2 ^ (prefixWord ++ tailWord_1291748).sum := by decide
  have hdescent : baseEnd_1291748 < baseStart_1291748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291758 : List Nat := [4, 1, 2, 1, 2, 1, 1, 4, 2, 5]
def baseStart_1291758 : Nat := 118140960795 + 1291758 * 2 ^ 59
def prefixEnd_1291758 : Nat := 4983230072969 + 3 ^ 40 * 1291758 * 2
def baseEnd_1291758 : Nat := 221097581096887408194773

theorem tailTrace_1291758 : CollatzResearch.WordTrace tailWord_1291758 prefixEnd_1291758 221097581096887408194773 := by
  unfold tailWord_1291758
  simp only [CollatzResearch.WordTrace]
  refine ⟨5889285606773606943434491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31409523236125903698317285 5889285606773606943434491)
  ·
    refine ⟨8833928410160410415151737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5889285606773606943434491 8833928410160410415151737)
    ·
      refine ⟨6625446307620307811363803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8833928410160410415151737 6625446307620307811363803)
      ·
        refine ⟨9938169461430461717045705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6625446307620307811363803 9938169461430461717045705)
        ·
          refine ⟨7453627096072846287784279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9938169461430461717045705 7453627096072846287784279)
          ·
            refine ⟨11180440644109269431676419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7453627096072846287784279 11180440644109269431676419)
            ·
              refine ⟨16770660966163904147514629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11180440644109269431676419 16770660966163904147514629)
              ·
                refine ⟨3144498931155732027658993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16770660966163904147514629 3144498931155732027658993)
                ·
                  refine ⟨2358374198366799020744245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3144498931155732027658993 2358374198366799020744245)
                  ·
                    refine ⟨221097581096887408194773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2358374198366799020744245 221097581096887408194773)
                    ·
                      rfl

theorem cell23_1291758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_1291758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291758 prefixEnd_1291758 := by exact prefixLift 1291758
  have htrace : WordTrace (prefixWord ++ tailWord_1291758) baseStart_1291758 baseEnd_1291758 := by
    simpa [prefixWord, tailWord_1291758, baseEnd_1291758] using wordTrace_append hprefix tailTrace_1291758
  have hstable : (prefixWord ++ tailWord_1291758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291758).length < 2 ^ (prefixWord ++ tailWord_1291758).sum := by decide
  have hdescent : baseEnd_1291758 < baseStart_1291758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291762 : List Nat := [3, 2, 1, 4, 1, 1, 4, 2, 5]
def baseStart_1291762 : Nat := 118140960795 + 1291762 * 2 ^ 59
def prefixEnd_1291762 : Nat := 4983230072969 + 3 ^ 40 * 1291762 * 2
def baseEnd_1291762 : Nat := 73699421912586689881589

theorem tailTrace_1291762 : CollatzResearch.WordTrace tailWord_1291762 prefixEnd_1291762 73699421912586689881589 := by
  unfold tailWord_1291762
  simp only [CollatzResearch.WordTrace]
  refine ⟨11778607686543591057655385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31409620497449576153747693 11778607686543591057655385)
  ·
    refine ⟨8833955764907693293241539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11778607686543591057655385 8833955764907693293241539)
    ·
      refine ⟨13250933647361539939862309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8833955764907693293241539 13250933647361539939862309)
      ·
        refine ⟨2484550058880288738724183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13250933647361539939862309 2484550058880288738724183)
        ·
          refine ⟨3726825088320433108086275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2484550058880288738724183 3726825088320433108086275)
          ·
            refine ⟨5590237632480649662129413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3726825088320433108086275 5590237632480649662129413)
            ·
              refine ⟨1048169556090121811649265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5590237632480649662129413 1048169556090121811649265)
              ·
                refine ⟨786127167067591358736949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1048169556090121811649265 786127167067591358736949)
                ·
                  refine ⟨73699421912586689881589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 786127167067591358736949 73699421912586689881589)
                  ·
                    rfl

theorem cell23_1291762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2, 5].length) (baseStart_1291762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291762 prefixEnd_1291762 := by exact prefixLift 1291762
  have htrace : WordTrace (prefixWord ++ tailWord_1291762) baseStart_1291762 baseEnd_1291762 := by
    simpa [prefixWord, tailWord_1291762, baseEnd_1291762] using wordTrace_append hprefix tailTrace_1291762
  have hstable : (prefixWord ++ tailWord_1291762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291762).length < 2 ^ (prefixWord ++ tailWord_1291762).sum := by decide
  have hdescent : baseEnd_1291762 < baseStart_1291762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291795 : List Nat := [1, 1, 1, 2, 1, 8, 1, 1, 2, 1, 4]
def baseStart_1291795 : Nat := 118140960795 + 1291795 * 2 ^ 59
def prefixEnd_1291795 : Nat := 4983230072969 + 3 ^ 40 * 1291795 * 2
def baseEnd_1291795 : Nat := 663311742074878579821649

theorem tailTrace_1291795 : CollatzResearch.WordTrace tailWord_1291795 prefixEnd_1291795 663311742074878579821649 := by
  unfold tailWord_1291795
  simp only [CollatzResearch.WordTrace]
  refine ⟨47115634355054810866572839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31410422903369873911048559 47115634355054810866572839)
  ·
    refine ⟨70673451532582216299859259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47115634355054810866572839 70673451532582216299859259)
    ·
      refine ⟨106010177298873324449788889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70673451532582216299859259 106010177298873324449788889)
      ·
        refine ⟨79507632974154993337341667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106010177298873324449788889 79507632974154993337341667)
        ·
          refine ⟨119261449461232490006012501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79507632974154993337341667 119261449461232490006012501)
          ·
            refine ⟨1397595110873818242257959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 119261449461232490006012501 1397595110873818242257959)
            ·
              refine ⟨2096392666310727363386939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1397595110873818242257959 2096392666310727363386939)
              ·
                refine ⟨3144588999466091045080409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2096392666310727363386939 3144588999466091045080409)
                ·
                  refine ⟨2358441749599568283810307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3144588999466091045080409 2358441749599568283810307)
                  ·
                    refine ⟨3537662624399352425715461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2358441749599568283810307 3537662624399352425715461)
                    ·
                      refine ⟨663311742074878579821649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3537662624399352425715461 663311742074878579821649)
                      ·
                        rfl

theorem cell23_1291795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 1, 4].length) (baseStart_1291795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291795 prefixEnd_1291795 := by exact prefixLift 1291795
  have htrace : WordTrace (prefixWord ++ tailWord_1291795) baseStart_1291795 baseEnd_1291795 := by
    simpa [prefixWord, tailWord_1291795, baseEnd_1291795] using wordTrace_append hprefix tailTrace_1291795
  have hstable : (prefixWord ++ tailWord_1291795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291795).length < 2 ^ (prefixWord ++ tailWord_1291795).sum := by decide
  have hdescent : baseEnd_1291795 < baseStart_1291795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291808 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 6]
def baseStart_1291808 : Nat := 118140960795 + 1291808 * 2 ^ 59
def prefixEnd_1291808 : Nat := 4983230072969 + 3 ^ 40 * 1291808 * 2
def baseEnd_1291808 : Nat := 663318417323387028959089

theorem tailTrace_1291808 : CollatzResearch.WordTrace tailWord_1291808 prefixEnd_1291808 663318417323387028959089 := by
  unfold tailWord_1291808
  simp only [CollatzResearch.WordTrace]
  refine ⟨23558054252003857043398039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31410739002671809391197385 23558054252003857043398039)
  ·
    refine ⟨35337081378005785565097059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23558054252003857043398039 35337081378005785565097059)
    ·
      refine ⟨53005622067008678347645589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35337081378005785565097059 53005622067008678347645589)
      ·
        refine ⟨2484638534391031797545887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 53005622067008678347645589 2484638534391031797545887)
        ·
          refine ⟨3726957801586547696318831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2484638534391031797545887 3726957801586547696318831)
          ·
            refine ⟨5590436702379821544478247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3726957801586547696318831 5590436702379821544478247)
            ·
              refine ⟨8385655053569732316717371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5590436702379821544478247 8385655053569732316717371)
              ·
                refine ⟨12578482580354598475076057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8385655053569732316717371 12578482580354598475076057)
                ·
                  refine ⟨9433861935265948856307043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12578482580354598475076057 9433861935265948856307043)
                  ·
                    refine ⟨14150792902898923284460565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9433861935265948856307043 14150792902898923284460565)
                    ·
                      refine ⟨663318417323387028959089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14150792902898923284460565 663318417323387028959089)
                      ·
                        rfl

theorem cell23_1291808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_1291808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291808 prefixEnd_1291808 := by exact prefixLift 1291808
  have htrace : WordTrace (prefixWord ++ tailWord_1291808) baseStart_1291808 baseEnd_1291808 := by
    simpa [prefixWord, tailWord_1291808, baseEnd_1291808] using wordTrace_append hprefix tailTrace_1291808
  have hstable : (prefixWord ++ tailWord_1291808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291808).length < 2 ^ (prefixWord ++ tailWord_1291808).sum := by decide
  have hdescent : baseEnd_1291808 < baseStart_1291808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291818 : List Nat := [3, 1, 4, 1, 1, 1, 3, 1, 8]
def baseStart_1291818 : Nat := 118140960795 + 1291818 * 2 ^ 59
def prefixEnd_1291818 : Nat := 4983230072969 + 3 ^ 40 * 1291818 * 2
def baseEnd_1291818 : Nat := 73702616903325776648227

theorem tailTrace_1291818 : CollatzResearch.WordTrace tailWord_1291818 prefixEnd_1291818 73702616903325776648227 := by
  unfold tailWord_1291818
  simp only [CollatzResearch.WordTrace]
  refine ⟨11779118308492871448665027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31410982155980990529773405 11779118308492871448665027)
  ·
    refine ⟨17668677462739307172997541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11779118308492871448665027 17668677462739307172997541)
    ·
      refine ⟨3312877024263620094937039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17668677462739307172997541 3312877024263620094937039)
      ·
        refine ⟨4969315536395430142405559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3312877024263620094937039 4969315536395430142405559)
        ·
          refine ⟨7453973304593145213608339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4969315536395430142405559 7453973304593145213608339)
          ·
            refine ⟨11180959956889717820412509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7453973304593145213608339 11180959956889717820412509)
            ·
              refine ⟨4192859983833644182654691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11180959956889717820412509 4192859983833644182654691)
              ·
                refine ⟨6289289975750466273982037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4192859983833644182654691 6289289975750466273982037)
                ·
                  refine ⟨73702616903325776648227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6289289975750466273982037 73702616903325776648227)
                  ·
                    rfl

theorem cell23_1291818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 8].length) (baseStart_1291818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291818 prefixEnd_1291818 := by exact prefixLift 1291818
  have htrace : WordTrace (prefixWord ++ tailWord_1291818) baseStart_1291818 baseEnd_1291818 := by
    simpa [prefixWord, tailWord_1291818, baseEnd_1291818] using wordTrace_append hprefix tailTrace_1291818
  have hstable : (prefixWord ++ tailWord_1291818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291818).length < 2 ^ (prefixWord ++ tailWord_1291818).sum := by decide
  have hdescent : baseEnd_1291818 < baseStart_1291818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291822 : List Nat := [4, 1, 3, 1, 2, 2, 2, 1, 3, 4]
def baseStart_1291822 : Nat := 118140960795 + 1291822 * 2 ^ 59
def prefixEnd_1291822 : Nat := 4983230072969 + 3 ^ 40 * 1291822 * 2
def baseEnd_1291822 : Nat := 221108535350849991394675

theorem tailTrace_1291822 : CollatzResearch.WordTrace tailWord_1291822 prefixEnd_1291822 221108535350849991394675 := by
  unfold tailWord_1291822
  simp only [CollatzResearch.WordTrace]
  refine ⟨5889577390744624309725715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31411079417304662985203813 5889577390744624309725715)
  ·
    refine ⟨8834366086116936464588573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5889577390744624309725715 8834366086116936464588573)
    ·
      refine ⟨3312887282293851174220715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8834366086116936464588573 3312887282293851174220715)
      ·
        refine ⟨4969330923440776761331073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3312887282293851174220715 4969330923440776761331073)
        ·
          refine ⟨3726998192580582570998305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4969330923440776761331073 3726998192580582570998305)
          ·
            refine ⟨2795248644435436928248729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3726998192580582570998305 2795248644435436928248729)
            ·
              refine ⟨2096436483326577696186547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2795248644435436928248729 2096436483326577696186547)
              ·
                refine ⟨3144654724989866544279821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2096436483326577696186547 3144654724989866544279821)
                ·
                  refine ⟨1179245521871199954104933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3144654724989866544279821 1179245521871199954104933)
                  ·
                    refine ⟨221108535350849991394675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1179245521871199954104933 221108535350849991394675)
                    ·
                      rfl

theorem cell23_1291822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_1291822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291822 prefixEnd_1291822 := by exact prefixLift 1291822
  have htrace : WordTrace (prefixWord ++ tailWord_1291822) baseStart_1291822 baseEnd_1291822 := by
    simpa [prefixWord, tailWord_1291822, baseEnd_1291822] using wordTrace_append hprefix tailTrace_1291822
  have hstable : (prefixWord ++ tailWord_1291822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291822).length < 2 ^ (prefixWord ++ tailWord_1291822).sum := by decide
  have hdescent : baseEnd_1291822 < baseStart_1291822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291845 : List Nat := [1, 3, 1, 1, 1, 4, 1, 4, 3, 1, 3]
def baseStart_1291845 : Nat := 118140960795 + 1291845 * 2 ^ 59
def prefixEnd_1291845 : Nat := 4983230072969 + 3 ^ 40 * 1291845 * 2
def baseEnd_1291845 : Nat := 663337416107603384196419

theorem tailTrace_1291845 : CollatzResearch.WordTrace tailWord_1291845 prefixEnd_1291845 663337416107603384196419 := by
  unfold tailWord_1291845
  simp only [CollatzResearch.WordTrace]
  refine ⟨47117458004873669405892989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31411638669915779603928659 47117458004873669405892989)
  ·
    refine ⟨17669046751827626027209871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47117458004873669405892989 17669046751827626027209871)
    ·
      refine ⟨26503570127741439040814807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17669046751827626027209871 26503570127741439040814807)
      ·
        refine ⟨39755355191612158561222211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26503570127741439040814807 39755355191612158561222211)
        ·
          refine ⟨59633032787418237841833317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39755355191612158561222211 59633032787418237841833317)
          ·
            refine ⟨11181193647640919595343747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59633032787418237841833317 11181193647640919595343747)
            ·
              refine ⟨16771790471461379393015621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11181193647640919595343747 16771790471461379393015621)
              ·
                refine ⟨3144710713399008636190429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16771790471461379393015621 3144710713399008636190429)
                ·
                  refine ⟨1179266517524628238571411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3144710713399008636190429 1179266517524628238571411)
                  ·
                    refine ⟨1768899776286942357857117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1179266517524628238571411 1768899776286942357857117)
                    ·
                      refine ⟨663337416107603384196419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1768899776286942357857117 663337416107603384196419)
                      ·
                        rfl

theorem cell23_1291845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3, 1, 3].length) (baseStart_1291845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291845 prefixEnd_1291845 := by exact prefixLift 1291845
  have htrace : WordTrace (prefixWord ++ tailWord_1291845) baseStart_1291845 baseEnd_1291845 := by
    simpa [prefixWord, tailWord_1291845, baseEnd_1291845] using wordTrace_append hprefix tailTrace_1291845
  have hstable : (prefixWord ++ tailWord_1291845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291845).length < 2 ^ (prefixWord ++ tailWord_1291845).sum := by decide
  have hdescent : baseEnd_1291845 < baseStart_1291845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291855 : List Nat := [1, 1, 2, 1, 1, 2, 3, 5, 2, 3, 2]
def baseStart_1291855 : Nat := 118140960795 + 1291855 * 2 ^ 59
def prefixEnd_1291855 : Nat := 4983230072969 + 3 ^ 40 * 1291855 * 2
def baseEnd_1291855 : Nat := 663342550914148345071373

theorem tailTrace_1291855 : CollatzResearch.WordTrace tailWord_1291855 prefixEnd_1291855 663342550914148345071373 := by
  unfold tailWord_1291855
  simp only [CollatzResearch.WordTrace]
  refine ⟨47117822734837441113757019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31411881823224960742504679 47117822734837441113757019)
  ·
    refine ⟨70676734102256161670635529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47117822734837441113757019 70676734102256161670635529)
    ·
      refine ⟨53007550576692121252976647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70676734102256161670635529 53007550576692121252976647)
      ·
        refine ⟨79511325865038181879464971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53007550576692121252976647 79511325865038181879464971)
        ·
          refine ⟨119266988797557272819197457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79511325865038181879464971 119266988797557272819197457)
          ·
            refine ⟨89450241598167954614398093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119266988797557272819197457 89450241598167954614398093)
            ·
              refine ⟨33543840599312982980399285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89450241598167954614398093 33543840599312982980399285)
              ·
                refine ⟨3144735056185592154412433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33543840599312982980399285 3144735056185592154412433)
                ·
                  refine ⟨2358551292139194115809325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3144735056185592154412433 2358551292139194115809325)
                  ·
                    refine ⟨884456734552197793428497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2358551292139194115809325 884456734552197793428497)
                    ·
                      refine ⟨663342550914148345071373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 884456734552197793428497 663342550914148345071373)
                      ·
                        rfl

theorem cell23_1291855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 3, 2].length) (baseStart_1291855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291855 prefixEnd_1291855 := by exact prefixLift 1291855
  have htrace : WordTrace (prefixWord ++ tailWord_1291855) baseStart_1291855 baseEnd_1291855 := by
    simpa [prefixWord, tailWord_1291855, baseEnd_1291855] using wordTrace_append hprefix tailTrace_1291855
  have hstable : (prefixWord ++ tailWord_1291855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291855).length < 2 ^ (prefixWord ++ tailWord_1291855).sum := by decide
  have hdescent : baseEnd_1291855 < baseStart_1291855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291912 : List Nat := [2, 1, 3, 5, 1, 1, 1, 2, 1, 6]
def baseStart_1291912 : Nat := 118140960795 + 1291912 * 2 ^ 59
def prefixEnd_1291912 : Nat := 4983230072969 + 3 ^ 40 * 1291912 * 2
def baseEnd_1291912 : Nat := 221123939770484874019537

theorem tailTrace_1291912 : CollatzResearch.WordTrace tailWord_1291912 prefixEnd_1291912 221123939770484874019537 := by
  unfold tailWord_1291912
  simp only [CollatzResearch.WordTrace]
  refine ⟨23559950847815469924290995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31413267797087293232387993 23559950847815469924290995)
  ·
    refine ⟨35339926271723204886436493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23559950847815469924290995 35339926271723204886436493)
    ·
      refine ⟨13252472351896201832413685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35339926271723204886436493 13252472351896201832413685)
      ·
        refine ⟨1242419282990268921788783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13252472351896201832413685 1242419282990268921788783)
        ·
          refine ⟨1863628924485403382683175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1242419282990268921788783 1863628924485403382683175)
          ·
            refine ⟨2795443386728105074024763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1863628924485403382683175 2795443386728105074024763)
            ·
              refine ⟨4193165080092157611037145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2795443386728105074024763 4193165080092157611037145)
              ·
                refine ⟨3144873810069118208277859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4193165080092157611037145 3144873810069118208277859)
                ·
                  refine ⟨4717310715103677312416789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3144873810069118208277859 4717310715103677312416789)
                  ·
                    refine ⟨221123939770484874019537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4717310715103677312416789 221123939770484874019537)
                    ·
                      rfl

theorem cell23_1291912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_1291912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291912 prefixEnd_1291912 := by exact prefixLift 1291912
  have htrace : WordTrace (prefixWord ++ tailWord_1291912) baseStart_1291912 baseEnd_1291912 := by
    simpa [prefixWord, tailWord_1291912, baseEnd_1291912] using wordTrace_append hprefix tailTrace_1291912
  have hstable : (prefixWord ++ tailWord_1291912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291912).length < 2 ^ (prefixWord ++ tailWord_1291912).sum := by decide
  have hdescent : baseEnd_1291912 < baseStart_1291912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291936 : List Nat := [2, 1, 1, 4, 3, 2, 1, 4, 1, 2, 2]
def baseStart_1291936 : Nat := 118140960795 + 1291936 * 2 ^ 59
def prefixEnd_1291936 : Nat := 4983230072969 + 3 ^ 40 * 1291936 * 2
def baseEnd_1291936 : Nat := 663384142847162528158501

theorem tailTrace_1291936 : CollatzResearch.WordTrace tailWord_1291936 prefixEnd_1291936 663384142847162528158501 := by
  unfold tailWord_1291936
  simp only [CollatzResearch.WordTrace]
  refine ⟨23560388523771995973727831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31413851365029327964970441 23560388523771995973727831)
  ·
    refine ⟨35340582785657993960591747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23560388523771995973727831 35340582785657993960591747)
    ·
      refine ⟨53010874178486990940887621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35340582785657993960591747 53010874178486990940887621)
      ·
        refine ⟨9939538908466310801416429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53010874178486990940887621 9939538908466310801416429)
        ·
          refine ⟨3727327090674866550531161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9939538908466310801416429 3727327090674866550531161)
          ·
            refine ⟨2795495318006149912898371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3727327090674866550531161 2795495318006149912898371)
            ·
              refine ⟨4193242977009224869347557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2795495318006149912898371 4193242977009224869347557)
              ·
                refine ⟨786233058189229663002667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4193242977009224869347557 786233058189229663002667)
                ·
                  refine ⟨1179349587283844494504001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 786233058189229663002667 1179349587283844494504001)
                  ·
                    refine ⟨884512190462883370878001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1179349587283844494504001 884512190462883370878001)
                    ·
                      refine ⟨663384142847162528158501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 884512190462883370878001 663384142847162528158501)
                      ·
                        rfl

theorem cell23_1291936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_1291936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291936 prefixEnd_1291936 := by exact prefixLift 1291936
  have htrace : WordTrace (prefixWord ++ tailWord_1291936) baseStart_1291936 baseEnd_1291936 := by
    simpa [prefixWord, tailWord_1291936, baseEnd_1291936] using wordTrace_append hprefix tailTrace_1291936
  have hstable : (prefixWord ++ tailWord_1291936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291936).length < 2 ^ (prefixWord ++ tailWord_1291936).sum := by decide
  have hdescent : baseEnd_1291936 < baseStart_1291936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291952 : List Nat := [2, 1, 1, 1, 2, 1, 6, 3, 2, 1, 3]
def baseStart_1291952 : Nat := 118140960795 + 1291952 * 2 ^ 59
def prefixEnd_1291952 : Nat := 4983230072969 + 3 ^ 40 * 1291952 * 2
def baseEnd_1291952 : Nat := 663392358537634465558427

theorem tailTrace_1291952 : CollatzResearch.WordTrace tailWord_1291952 prefixEnd_1291952 663392358537634465558427 := by
  unfold tailWord_1291952
  simp only [CollatzResearch.WordTrace]
  refine ⟨23560680307743013340019055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31414240410324017786692073 23560680307743013340019055)
  ·
    refine ⟨35341020461614520010028583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23560680307743013340019055 35341020461614520010028583)
    ·
      refine ⟨53011530692421780015042875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35341020461614520010028583 53011530692421780015042875)
      ·
        refine ⟨79517296038632670022564313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53011530692421780015042875 79517296038632670022564313)
        ·
          refine ⟨59637972028974502516923235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79517296038632670022564313 59637972028974502516923235)
          ·
            refine ⟨89456958043461753775384853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59637972028974502516923235 89456958043461753775384853)
            ·
              refine ⟨4193294908287269708221165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 89456958043461753775384853 4193294908287269708221165)
              ·
                refine ⟨1572485590607726140582937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4193294908287269708221165 1572485590607726140582937)
                ·
                  refine ⟨1179364192955794605437203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1572485590607726140582937 1179364192955794605437203)
                  ·
                    refine ⟨1769046289433691908155805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1179364192955794605437203 1769046289433691908155805)
                    ·
                      refine ⟨663392358537634465558427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1769046289433691908155805 663392358537634465558427)
                      ·
                        rfl

theorem cell23_1291952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 2, 1, 3].length) (baseStart_1291952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291952 prefixEnd_1291952 := by exact prefixLift 1291952
  have htrace : WordTrace (prefixWord ++ tailWord_1291952) baseStart_1291952 baseEnd_1291952 := by
    simpa [prefixWord, tailWord_1291952, baseEnd_1291952] using wordTrace_append hprefix tailTrace_1291952
  have hstable : (prefixWord ++ tailWord_1291952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291952).length < 2 ^ (prefixWord ++ tailWord_1291952).sum := by decide
  have hdescent : baseEnd_1291952 < baseStart_1291952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291962 : List Nat := [3, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2]
def baseStart_1291962 : Nat := 118140960795 + 1291962 * 2 ^ 59
def prefixEnd_1291962 : Nat := 4983230072969 + 3 ^ 40 * 1291962 * 2
def baseEnd_1291962 : Nat := 663397493344179426433381

theorem tailTrace_1291962 : CollatzResearch.WordTrace tailWord_1291962 prefixEnd_1291962 663397493344179426433381 := by
  unfold tailWord_1291962
  simp only [CollatzResearch.WordTrace]
  refine ⟨11780431336362449596975535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31414483563633198925268093 11780431336362449596975535)
  ·
    refine ⟨17670647004543674395463303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11780431336362449596975535 17670647004543674395463303)
    ·
      refine ⟨26505970506815511593194955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17670647004543674395463303 26505970506815511593194955)
      ·
        refine ⟨39758955760223267389792433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26505970506815511593194955 39758955760223267389792433)
        ·
          refine ⟨29819216820167450542344325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39758955760223267389792433 29819216820167450542344325)
          ·
            refine ⟨5591103153781396976689561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29819216820167450542344325 5591103153781396976689561)
            ·
              refine ⟨4193327365336047732517171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5591103153781396976689561 4193327365336047732517171)
              ·
                refine ⟨6289991048004071598775757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4193327365336047732517171 6289991048004071598775757)
                ·
                  refine ⟨2358746643001526849540909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6289991048004071598775757 2358746643001526849540909)
                  ·
                    refine ⟨884529991125572568577841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2358746643001526849540909 884529991125572568577841)
                    ·
                      refine ⟨663397493344179426433381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 884529991125572568577841 663397493344179426433381)
                      ·
                        rfl

theorem cell23_1291962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2].length) (baseStart_1291962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291962 prefixEnd_1291962 := by exact prefixLift 1291962
  have htrace : WordTrace (prefixWord ++ tailWord_1291962) baseStart_1291962 baseEnd_1291962 := by
    simpa [prefixWord, tailWord_1291962, baseEnd_1291962] using wordTrace_append hprefix tailTrace_1291962
  have hstable : (prefixWord ++ tailWord_1291962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291962).length < 2 ^ (prefixWord ++ tailWord_1291962).sum := by decide
  have hdescent : baseEnd_1291962 < baseStart_1291962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291968 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 1, 8]
def baseStart_1291968 : Nat := 118140960795 + 1291968 * 2 ^ 59
def prefixEnd_1291968 : Nat := 4983230072969 + 3 ^ 40 * 1291968 * 2
def baseEnd_1291968 : Nat := 221133524742702134319451

theorem tailTrace_1291968 : CollatzResearch.WordTrace tailWord_1291968 prefixEnd_1291968 221133524742702134319451 := by
  unfold tailWord_1291968
  simp only [CollatzResearch.WordTrace]
  refine ⟨23560972091714030706310279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31414629455618707608413705 23560972091714030706310279)
  ·
    refine ⟨35341458137571046059465419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23560972091714030706310279 35341458137571046059465419)
    ·
      refine ⟨53012187206356569089198129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35341458137571046059465419 53012187206356569089198129)
      ·
        refine ⟨39759140404767426816898597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53012187206356569089198129 39759140404767426816898597)
        ·
          refine ⟨7454838825893892528168487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39759140404767426816898597 7454838825893892528168487)
          ·
            refine ⟨11182258238840838792252731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7454838825893892528168487 11182258238840838792252731)
            ·
              refine ⟨16773387358261258188379097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11182258238840838792252731 16773387358261258188379097)
              ·
                refine ⟨12580040518695943641284323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16773387358261258188379097 12580040518695943641284323)
                ·
                  refine ⟨18870060778043915461926485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12580040518695943641284323 18870060778043915461926485)
                  ·
                    refine ⟨221133524742702134319451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18870060778043915461926485 221133524742702134319451)
                    ·
                      rfl

theorem cell23_1291968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 8].length) (baseStart_1291968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291968 prefixEnd_1291968 := by exact prefixLift 1291968
  have htrace : WordTrace (prefixWord ++ tailWord_1291968) baseStart_1291968 baseEnd_1291968 := by
    simpa [prefixWord, tailWord_1291968, baseEnd_1291968] using wordTrace_append hprefix tailTrace_1291968
  have hstable : (prefixWord ++ tailWord_1291968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291968).length < 2 ^ (prefixWord ++ tailWord_1291968).sum := by decide
  have hdescent : baseEnd_1291968 < baseStart_1291968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291970 : List Nat := [3, 5, 1, 2, 1, 2, 2, 1, 1, 1, 4]
def baseStart_1291970 : Nat := 118140960795 + 1291970 * 2 ^ 59
def prefixEnd_1291970 : Nat := 4983230072969 + 3 ^ 40 * 1291970 * 2
def baseEnd_1291970 : Nat := 663401601189415395133345

theorem tailTrace_1291970 : CollatzResearch.WordTrace tailWord_1291970 prefixEnd_1291970 663401601189415395133345 := by
  unfold tailWord_1291970
  simp only [CollatzResearch.WordTrace]
  refine ⟨11780504282355203938548341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31414678086280543836128909 11780504282355203938548341)
  ·
    refine ⟨1104422276470800369238907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11780504282355203938548341 1104422276470800369238907)
    ·
      refine ⟨1656633414706200553858361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1104422276470800369238907 1656633414706200553858361)
      ·
        refine ⟨1242475061029650415393771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1656633414706200553858361 1242475061029650415393771)
        ·
          refine ⟨1863712591544475623090657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1242475061029650415393771 1863712591544475623090657)
          ·
            refine ⟨1397784443658356717317993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1863712591544475623090657 1397784443658356717317993)
            ·
              refine ⟨1048338332743767537988495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1397784443658356717317993 1048338332743767537988495)
              ·
                refine ⟨1572507499115651306982743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1048338332743767537988495 1572507499115651306982743)
                ·
                  refine ⟨2358761248673476960474115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1572507499115651306982743 2358761248673476960474115)
                  ·
                    refine ⟨3538141873010215440711173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2358761248673476960474115 3538141873010215440711173)
                    ·
                      refine ⟨663401601189415395133345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3538141873010215440711173 663401601189415395133345)
                      ·
                        rfl

theorem cell23_1291970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_1291970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291970 prefixEnd_1291970 := by exact prefixLift 1291970
  have htrace : WordTrace (prefixWord ++ tailWord_1291970) baseStart_1291970 baseEnd_1291970 := by
    simpa [prefixWord, tailWord_1291970, baseEnd_1291970] using wordTrace_append hprefix tailTrace_1291970
  have hstable : (prefixWord ++ tailWord_1291970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291970).length < 2 ^ (prefixWord ++ tailWord_1291970).sum := by decide
  have hdescent : baseEnd_1291970 < baseStart_1291970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291986 : List Nat := [3, 2, 2, 2, 2, 3, 1, 2, 2, 1, 3]
def baseStart_1291986 : Nat := 118140960795 + 1291986 * 2 ^ 59
def prefixEnd_1291986 : Nat := 4983230072969 + 3 ^ 40 * 1291986 * 2
def baseEnd_1291986 : Nat := 663409816879887332533271

theorem tailTrace_1291986 : CollatzResearch.WordTrace tailWord_1291986 prefixEnd_1291986 663409816879887332533271 := by
  unfold tailWord_1291986
  simp only [CollatzResearch.WordTrace]
  refine ⟨11780650174340712621693953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31415067131575233657850541 11780650174340712621693953)
  ·
    refine ⟨8835487630755534466270465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11780650174340712621693953 8835487630755534466270465)
    ·
      refine ⟨6626615723066650849702849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8835487630755534466270465 6626615723066650849702849)
      ·
        refine ⟨4969961792299988137277137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6626615723066650849702849 4969961792299988137277137)
        ·
          refine ⟨3727471344224991102957853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4969961792299988137277137 3727471344224991102957853)
          ·
            refine ⟨1397801754084371663609195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3727471344224991102957853 1397801754084371663609195)
            ·
              refine ⟨2096702631126557495413793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1397801754084371663609195 2096702631126557495413793)
              ·
                refine ⟨1572526973344918121560345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2096702631126557495413793 1572526973344918121560345)
                ·
                  refine ⟨1179395230008688591170259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1572526973344918121560345 1179395230008688591170259)
                  ·
                    refine ⟨1769092845013032886755389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1179395230008688591170259 1769092845013032886755389)
                    ·
                      refine ⟨663409816879887332533271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1769092845013032886755389 663409816879887332533271)
                      ·
                        rfl

theorem cell23_1291986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_1291986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1291986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1291986 prefixEnd_1291986 := by exact prefixLift 1291986
  have htrace : WordTrace (prefixWord ++ tailWord_1291986) baseStart_1291986 baseEnd_1291986 := by
    simpa [prefixWord, tailWord_1291986, baseEnd_1291986] using wordTrace_append hprefix tailTrace_1291986
  have hstable : (prefixWord ++ tailWord_1291986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291986).length < 2 ^ (prefixWord ++ tailWord_1291986).sum := by decide
  have hdescent : baseEnd_1291986 < baseStart_1291986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292005 : List Nat := [1, 3, 1, 4, 1, 1, 1, 3, 2, 2, 4]
def baseStart_1292005 : Nat := 118140960795 + 1292005 * 2 ^ 59
def prefixEnd_1292005 : Nat := 4983230072969 + 3 ^ 40 * 1292005 * 2
def baseEnd_1292005 : Nat := 663419573012322758195683

theorem tailTrace_1292005 : CollatzResearch.WordTrace tailWord_1292005 prefixEnd_1292005 663419573012322758195683 := by
  unfold tailWord_1292005
  simp only [CollatzResearch.WordTrace]
  refine ⟨47123293684294016731717469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31415529122862677821144979 47123293684294016731717469)
  ·
    refine ⟨17671235131610256274394051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47123293684294016731717469 17671235131610256274394051)
    ·
      refine ⟨26506852697415384411591077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17671235131610256274394051 26506852697415384411591077)
      ·
        refine ⟨4970034880765384577173327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26506852697415384411591077 4970034880765384577173327)
        ·
          refine ⟨7455052321148076865759991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4970034880765384577173327 7455052321148076865759991)
          ·
            refine ⟨11182578481722115298639987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7455052321148076865759991 11182578481722115298639987)
            ·
              refine ⟨16773867722583172947959981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11182578481722115298639987 16773867722583172947959981)
              ·
                refine ⟨6290200395968689855484993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16773867722583172947959981 6290200395968689855484993)
                ·
                  refine ⟨4717650296976517391613745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6290200395968689855484993 4717650296976517391613745)
                  ·
                    refine ⟨3538237722732388043710309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4717650296976517391613745 3538237722732388043710309)
                    ·
                      refine ⟨663419573012322758195683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3538237722732388043710309 663419573012322758195683)
                      ·
                        rfl

theorem cell23_1292005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_1292005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292005 prefixEnd_1292005 := by exact prefixLift 1292005
  have htrace : WordTrace (prefixWord ++ tailWord_1292005) baseStart_1292005 baseEnd_1292005 := by
    simpa [prefixWord, tailWord_1292005, baseEnd_1292005] using wordTrace_append hprefix tailTrace_1292005
  have hstable : (prefixWord ++ tailWord_1292005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292005).length < 2 ^ (prefixWord ++ tailWord_1292005).sum := by decide
  have hdescent : baseEnd_1292005 < baseStart_1292005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292055 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 7]
def baseStart_1292055 : Nat := 118140960795 + 1292055 * 2 ^ 59
def prefixEnd_1292055 : Nat := 4983230072969 + 3 ^ 40 * 1292055 * 2
def baseEnd_1292055 : Nat := 663445247045047562570453

theorem tailTrace_1292055 : CollatzResearch.WordTrace tailWord_1292055 prefixEnd_1292055 663445247045047562570453 := by
  unfold tailWord_1292055
  simp only [CollatzResearch.WordTrace]
  refine ⟨47125117334112875271037619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31416744889408583514025079 47125117334112875271037619)
  ·
    refine ⟨70687676001169312906556429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47125117334112875271037619 70687676001169312906556429)
    ·
      refine ⟨26507878500438492339958661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70687676001169312906556429 26507878500438492339958661)
      ·
        refine ⟨4970227218832217313742249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26507878500438492339958661 4970227218832217313742249)
        ·
          refine ⟨3727670414124162985306687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4970227218832217313742249 3727670414124162985306687)
          ·
            refine ⟨5591505621186244477960031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3727670414124162985306687 5591505621186244477960031)
            ·
              refine ⟨8387258431779366716940047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5591505621186244477960031 8387258431779366716940047)
              ·
                refine ⟨12580887647669050075410071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8387258431779366716940047 12580887647669050075410071)
                ·
                  refine ⟨18871331471503575113115107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12580887647669050075410071 18871331471503575113115107)
                  ·
                    refine ⟨28306997207255362669672661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18871331471503575113115107 28306997207255362669672661)
                    ·
                      refine ⟨663445247045047562570453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28306997207255362669672661 663445247045047562570453)
                      ·
                        rfl

theorem cell23_1292055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_1292055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292055 prefixEnd_1292055 := by exact prefixLift 1292055
  have htrace : WordTrace (prefixWord ++ tailWord_1292055) baseStart_1292055 baseEnd_1292055 := by
    simpa [prefixWord, tailWord_1292055, baseEnd_1292055] using wordTrace_append hprefix tailTrace_1292055
  have hstable : (prefixWord ++ tailWord_1292055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292055).length < 2 ^ (prefixWord ++ tailWord_1292055).sum := by decide
  have hdescent : baseEnd_1292055 < baseStart_1292055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292082 : List Nat := [3, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4]
def baseStart_1292082 : Nat := 118140960795 + 1292082 * 2 ^ 59
def prefixEnd_1292082 : Nat := 4983230072969 + 3 ^ 40 * 1292082 * 2
def baseEnd_1292082 : Nat := 663459111022718956932829

theorem tailTrace_1292082 : CollatzResearch.WordTrace tailWord_1292082 prefixEnd_1292082 663459111022718956932829 := by
  unfold tailWord_1292082
  simp only [CollatzResearch.WordTrace]
  refine ⟨11781525526253764720567625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31417401403343372588180333 11781525526253764720567625)
  ·
    refine ⟨8836144144690323540425719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11781525526253764720567625 8836144144690323540425719)
    ·
      refine ⟨13254216217035485310638579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8836144144690323540425719 13254216217035485310638579)
      ·
        refine ⟨19881324325553227965957869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13254216217035485310638579 19881324325553227965957869)
        ·
          refine ⟨7455496622082460487234201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19881324325553227965957869 7455496622082460487234201)
          ·
            refine ⟨5591622466561845365425651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7455496622082460487234201 5591622466561845365425651)
            ·
              refine ⟨8387433699842768048138477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5591622466561845365425651 8387433699842768048138477)
              ·
                refine ⟨3145287637441038018051929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8387433699842768048138477 3145287637441038018051929)
                ·
                  refine ⟨2358965728080778513538947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3145287637441038018051929 2358965728080778513538947)
                  ·
                    refine ⟨3538448592121167770308421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2358965728080778513538947 3538448592121167770308421)
                    ·
                      refine ⟨663459111022718956932829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3538448592121167770308421 663459111022718956932829)
                      ·
                        rfl

theorem cell23_1292082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_1292082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292082 prefixEnd_1292082 := by exact prefixLift 1292082
  have htrace : WordTrace (prefixWord ++ tailWord_1292082) baseStart_1292082 baseEnd_1292082 := by
    simpa [prefixWord, tailWord_1292082, baseEnd_1292082] using wordTrace_append hprefix tailTrace_1292082
  have hstable : (prefixWord ++ tailWord_1292082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292082).length < 2 ^ (prefixWord ++ tailWord_1292082).sum := by decide
  have hdescent : baseEnd_1292082 < baseStart_1292082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292115 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 4, 5, 3]
def baseStart_1292115 : Nat := 118140960795 + 1292115 * 2 ^ 59
def prefixEnd_1292115 : Nat := 4983230072969 + 3 ^ 40 * 1292115 * 2
def baseEnd_1292115 : Nat := 663476055884317327820177

theorem tailTrace_1292115 : CollatzResearch.WordTrace tailWord_1292115 prefixEnd_1292115 663476055884317327820177 := by
  unfold tailWord_1292115
  simp only [CollatzResearch.WordTrace]
  refine ⟨47127305713895505518221799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31418203809263670345481199 47127305713895505518221799)
  ·
    refine ⟨70690958570843258277332699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47127305713895505518221799 70690958570843258277332699)
    ·
      refine ⟨106036437856264887415999049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70690958570843258277332699 106036437856264887415999049)
      ·
        refine ⟨79527328392198665561999287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106036437856264887415999049 79527328392198665561999287)
        ·
          refine ⟨119290992588297998342998931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79527328392198665561999287 119290992588297998342998931)
          ·
            refine ⟨178936488882446997514498397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119290992588297998342998931 178936488882446997514498397)
            ·
              refine ⟨67101183330917624067936899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178936488882446997514498397 67101183330917624067936899)
              ·
                refine ⟨100651774996376436101905349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67101183330917624067936899 100651774996376436101905349)
                ·
                  refine ⟨18872207811820581769107253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100651774996376436101905349 18872207811820581769107253)
                  ·
                    refine ⟨1769269482358179540853805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18872207811820581769107253 1769269482358179540853805)
                    ·
                      refine ⟨663476055884317327820177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1769269482358179540853805 663476055884317327820177)
                      ·
                        rfl

theorem cell23_1292115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5, 3].length) (baseStart_1292115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292115 prefixEnd_1292115 := by exact prefixLift 1292115
  have htrace : WordTrace (prefixWord ++ tailWord_1292115) baseStart_1292115 baseEnd_1292115 := by
    simpa [prefixWord, tailWord_1292115, baseEnd_1292115] using wordTrace_append hprefix tailTrace_1292115
  have hstable : (prefixWord ++ tailWord_1292115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292115).length < 2 ^ (prefixWord ++ tailWord_1292115).sum := by decide
  have hdescent : baseEnd_1292115 < baseStart_1292115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292149 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 5, 1, 3]
def baseStart_1292149 : Nat := 118140960795 + 1292149 * 2 ^ 59
def prefixEnd_1292149 : Nat := 4983230072969 + 3 ^ 40 * 1292149 * 2
def baseEnd_1292149 : Nat := 663493514226570194795021

theorem tailTrace_1292149 : CollatzResearch.WordTrace tailWord_1292149 prefixEnd_1292149 663493514226570194795021 := by
  unfold tailWord_1292149
  simp only [CollatzResearch.WordTrace]
  refine ⟨47128545795772329324959501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31419030530514886216639667 47128545795772329324959501)
  ·
    refine ⟨17673204673414623496859813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47128545795772329324959501 17673204673414623496859813)
    ·
      refine ⟨3313725876265241905661215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17673204673414623496859813 3313725876265241905661215)
      ·
        refine ⟨4970588814397862858491823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3313725876265241905661215 4970588814397862858491823)
        ·
          refine ⟨7455883221596794287737735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4970588814397862858491823 7455883221596794287737735)
          ·
            refine ⟨11183824832395191431606603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7455883221596794287737735 11183824832395191431606603)
            ·
              refine ⟨16775737248592787147409905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11183824832395191431606603 16775737248592787147409905)
              ·
                refine ⟨12581802936444590360557429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16775737248592787147409905 12581802936444590360557429)
                ·
                  refine ⟨1179544025291680346302259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12581802936444590360557429 1179544025291680346302259)
                  ·
                    refine ⟨1769316037937520519453389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1179544025291680346302259 1769316037937520519453389)
                    ·
                      refine ⟨663493514226570194795021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1769316037937520519453389 663493514226570194795021)
                      ·
                        rfl

theorem cell23_1292149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_1292149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292149 prefixEnd_1292149 := by exact prefixLift 1292149
  have htrace : WordTrace (prefixWord ++ tailWord_1292149) baseStart_1292149 baseEnd_1292149 := by
    simpa [prefixWord, tailWord_1292149, baseEnd_1292149] using wordTrace_append hprefix tailTrace_1292149
  have hstable : (prefixWord ++ tailWord_1292149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292149).length < 2 ^ (prefixWord ++ tailWord_1292149).sum := by decide
  have hdescent : baseEnd_1292149 < baseStart_1292149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292189 : List Nat := [1, 4, 2, 1, 2, 2, 1, 4, 1, 1, 4]
def baseStart_1292189 : Nat := 118140960795 + 1292189 * 2 ^ 59
def prefixEnd_1292189 : Nat := 4983230072969 + 3 ^ 40 * 1292189 * 2
def baseEnd_1292189 : Nat := 663514053452750038294837

theorem tailTrace_1292189 : CollatzResearch.WordTrace tailWord_1292189 prefixEnd_1292189 663514053452750038294837 := by
  unfold tailWord_1292189
  simp only [CollatzResearch.WordTrace]
  refine ⟨47130004715627416156415621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31420003143751610770943747 47130004715627416156415621)
  ·
    refine ⟨8836875884180140529327929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47130004715627416156415621 8836875884180140529327929)
    ·
      refine ⟨6627656913135105396995947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8836875884180140529327929 6627656913135105396995947)
      ·
        refine ⟨9941485369702658095493921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6627656913135105396995947 9941485369702658095493921)
        ·
          refine ⟨7456114027276993571620441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9941485369702658095493921 7456114027276993571620441)
          ·
            refine ⟨5592085520457745178715331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7456114027276993571620441 5592085520457745178715331)
            ·
              refine ⟨8388128280686617768072997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5592085520457745178715331 8388128280686617768072997)
              ·
                refine ⟨1572774052628740831513687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8388128280686617768072997 1572774052628740831513687)
                ·
                  refine ⟨2359161078943111247270531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1572774052628740831513687 2359161078943111247270531)
                  ·
                    refine ⟨3538741618414666870905797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2359161078943111247270531 3538741618414666870905797)
                    ·
                      refine ⟨663514053452750038294837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3538741618414666870905797 663514053452750038294837)
                      ·
                        rfl

theorem cell23_1292189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_1292189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292189 prefixEnd_1292189 := by exact prefixLift 1292189
  have htrace : WordTrace (prefixWord ++ tailWord_1292189) baseStart_1292189 baseEnd_1292189 := by
    simpa [prefixWord, tailWord_1292189, baseEnd_1292189] using wordTrace_append hprefix tailTrace_1292189
  have hstable : (prefixWord ++ tailWord_1292189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292189).length < 2 ^ (prefixWord ++ tailWord_1292189).sum := by decide
  have hdescent : baseEnd_1292189 < baseStart_1292189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292199 : List Nat := [1, 1, 6, 1, 2, 1, 1, 2, 4, 4]
def baseStart_1292199 : Nat := 118140960795 + 1292199 * 2 ^ 59
def prefixEnd_1292199 : Nat := 4983230072969 + 3 ^ 40 * 1292199 * 2
def baseEnd_1292199 : Nat := 221173062753098333056597

theorem tailTrace_1292199 : CollatzResearch.WordTrace tailWord_1292199 prefixEnd_1292199 221173062753098333056597 := by
  unfold tailWord_1292199
  simp only [CollatzResearch.WordTrace]
  refine ⟨47130369445591187864279651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31420246297060791909519767 47130369445591187864279651)
  ·
    refine ⟨70695554168386781796419477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47130369445591187864279651 70695554168386781796419477)
    ·
      refine ⟨3313854101643130396707163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 70695554168386781796419477 3313854101643130396707163)
      ·
        refine ⟨4970781152464695595060745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3313854101643130396707163 4970781152464695595060745)
        ·
          refine ⟨3728085864348521696295559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4970781152464695595060745 3728085864348521696295559)
          ·
            refine ⟨5592128796522782544443339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3728085864348521696295559 5592128796522782544443339)
            ·
              refine ⟨8388193194784173816665009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5592128796522782544443339 8388193194784173816665009)
              ·
                refine ⟨6291144896088130362498757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8388193194784173816665009 6291144896088130362498757)
                ·
                  refine ⟨1179589668016524442968517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6291144896088130362498757 1179589668016524442968517)
                  ·
                    refine ⟨221173062753098333056597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1179589668016524442968517 221173062753098333056597)
                    ·
                      rfl

theorem cell23_1292199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_1292199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292199 prefixEnd_1292199 := by exact prefixLift 1292199
  have htrace : WordTrace (prefixWord ++ tailWord_1292199) baseStart_1292199 baseEnd_1292199 := by
    simpa [prefixWord, tailWord_1292199, baseEnd_1292199] using wordTrace_append hprefix tailTrace_1292199
  have hstable : (prefixWord ++ tailWord_1292199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292199).length < 2 ^ (prefixWord ++ tailWord_1292199).sum := by decide
  have hdescent : baseEnd_1292199 < baseStart_1292199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292209 : List Nat := [1, 2, 2, 4, 2, 2, 2, 1, 1, 1, 5]
def baseStart_1292209 : Nat := 118140960795 + 1292209 * 2 ^ 59
def prefixEnd_1292209 : Nat := 4983230072969 + 3 ^ 40 * 1292209 * 2
def baseEnd_1292209 : Nat := 663524323065839960044745

theorem tailTrace_1292209 : CollatzResearch.WordTrace tailWord_1292209 prefixEnd_1292209 663524323065839960044745 := by
  unfold tailWord_1292209
  simp only [CollatzResearch.WordTrace]
  refine ⟨47130734175554959572143681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31420489450369973048095787 47130734175554959572143681)
  ·
    refine ⟨35348050631666219679107761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47130734175554959572143681 35348050631666219679107761)
    ·
      refine ⟨26511037973749664759330821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35348050631666219679107761 26511037973749664759330821)
      ·
        refine ⟨4970819620078062142374529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26511037973749664759330821 4970819620078062142374529)
        ·
          refine ⟨3728114715058546606780897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4970819620078062142374529 3728114715058546606780897)
          ·
            refine ⟨2796086036293909955085673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3728114715058546606780897 2796086036293909955085673)
            ·
              refine ⟨2097064527220432466314255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2796086036293909955085673 2097064527220432466314255)
              ·
                refine ⟨3145596790830648699471383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2097064527220432466314255 3145596790830648699471383)
                ·
                  refine ⟨4718395186245973049207075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3145596790830648699471383 4718395186245973049207075)
                  ·
                    refine ⟨7077592779368959573810613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4718395186245973049207075 7077592779368959573810613)
                    ·
                      refine ⟨663524323065839960044745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7077592779368959573810613 663524323065839960044745)
                      ·
                        rfl

theorem cell23_1292209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_1292209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292209 prefixEnd_1292209 := by exact prefixLift 1292209
  have htrace : WordTrace (prefixWord ++ tailWord_1292209) baseStart_1292209 baseEnd_1292209 := by
    simpa [prefixWord, tailWord_1292209, baseEnd_1292209] using wordTrace_append hprefix tailTrace_1292209
  have hstable : (prefixWord ++ tailWord_1292209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292209).length < 2 ^ (prefixWord ++ tailWord_1292209).sum := by decide
  have hdescent : baseEnd_1292209 < baseStart_1292209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292273 : List Nat := [1, 2, 2, 2, 5, 1, 2, 2, 2, 1, 3]
def baseStart_1292273 : Nat := 118140960795 + 1292273 * 2 ^ 59
def prefixEnd_1292273 : Nat := 4983230072969 + 3 ^ 40 * 1292273 * 2
def baseEnd_1292273 : Nat := 663557185827727709644451

theorem tailTrace_1292273 : CollatzResearch.WordTrace tailWord_1292273 prefixEnd_1292273 663557185827727709644451 := by
  unfold tailWord_1292273
  simp only [CollatzResearch.WordTrace]
  refine ⟨47133068447323098502473473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31422045631548732334982315 47133068447323098502473473)
  ·
    refine ⟨35349801335492323876855105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47133068447323098502473473 35349801335492323876855105)
    ·
      refine ⟨26512351001619242907641329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35349801335492323876855105 26512351001619242907641329)
      ·
        refine ⟨19884263251214432180730997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26512351001619242907641329 19884263251214432180730997)
        ·
          refine ⟨1864149679801353016943531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19884263251214432180730997 1864149679801353016943531)
          ·
            refine ⟨2796224519702029525415297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1864149679801353016943531 2796224519702029525415297)
            ·
              refine ⟨2097168389776522144061473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2796224519702029525415297 2097168389776522144061473)
              ·
                refine ⟨1572876292332391608046105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2097168389776522144061473 1572876292332391608046105)
                ·
                  refine ⟨1179657219249293706034579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1572876292332391608046105 1179657219249293706034579)
                  ·
                    refine ⟨1769485828873940559051869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1179657219249293706034579 1769485828873940559051869)
                    ·
                      refine ⟨663557185827727709644451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1769485828873940559051869 663557185827727709644451)
                      ·
                        rfl

theorem cell23_1292273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_1292273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292273 prefixEnd_1292273 := by exact prefixLift 1292273
  have htrace : WordTrace (prefixWord ++ tailWord_1292273) baseStart_1292273 baseEnd_1292273 := by
    simpa [prefixWord, tailWord_1292273, baseEnd_1292273] using wordTrace_append hprefix tailTrace_1292273
  have hstable : (prefixWord ++ tailWord_1292273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292273).length < 2 ^ (prefixWord ++ tailWord_1292273).sum := by decide
  have hdescent : baseEnd_1292273 < baseStart_1292273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292296 : List Nat := [2, 1, 3, 2, 1, 2, 4, 1, 1, 4, 2]
def baseStart_1292296 : Nat := 118140960795 + 1292296 * 2 ^ 59
def prefixEnd_1292296 : Nat := 4983230072969 + 3 ^ 40 * 1292296 * 2
def baseEnd_1292296 : Nat := 663568995882781119656845

theorem tailTrace_1292296 : CollatzResearch.WordTrace tailWord_1292296 prefixEnd_1292296 663568995882781119656845 := by
  unfold tailWord_1292296
  simp only [CollatzResearch.WordTrace]
  refine ⟨23566953663119886715280371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31422604884159848953707161 23566953663119886715280371)
  ·
    refine ⟨35350430494679830072920557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23566953663119886715280371 35350430494679830072920557)
    ·
      refine ⟨13256411435504936277345209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35350430494679830072920557 13256411435504936277345209)
      ·
        refine ⟨9942308576628702208008907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13256411435504936277345209 9942308576628702208008907)
        ·
          refine ⟨14913462864943053312013361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9942308576628702208008907 14913462864943053312013361)
          ·
            refine ⟨11185097148707289984010021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14913462864943053312013361 11185097148707289984010021)
            ·
              refine ⟨2097205715382616872001879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11185097148707289984010021 2097205715382616872001879)
              ·
                refine ⟨3145808573073925308002819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2097205715382616872001879 3145808573073925308002819)
                ·
                  refine ⟨4718712859610887962004229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3145808573073925308002819 4718712859610887962004229)
                  ·
                    refine ⟨884758661177041492875793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4718712859610887962004229 884758661177041492875793)
                    ·
                      refine ⟨663568995882781119656845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 884758661177041492875793 663568995882781119656845)
                      ·
                        rfl

theorem cell23_1292296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_1292296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292296 prefixEnd_1292296 := by exact prefixLift 1292296
  have htrace : WordTrace (prefixWord ++ tailWord_1292296) baseStart_1292296 baseEnd_1292296 := by
    simpa [prefixWord, tailWord_1292296, baseEnd_1292296] using wordTrace_append hprefix tailTrace_1292296
  have hstable : (prefixWord ++ tailWord_1292296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292296).length < 2 ^ (prefixWord ++ tailWord_1292296).sum := by decide
  have hdescent : baseEnd_1292296 < baseStart_1292296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292330 : List Nat := [3, 1, 4, 1, 2, 1, 3, 2, 2, 2, 2]
def baseStart_1292330 : Nat := 118140960795 + 1292330 * 2 ^ 59
def prefixEnd_1292330 : Nat := 4983230072969 + 3 ^ 40 * 1292330 * 2
def baseEnd_1292330 : Nat := 663586454225033986631689

theorem tailTrace_1292330 : CollatzResearch.WordTrace tailWord_1292330 prefixEnd_1292330 663586454225033986631689 := by
  unfold tailWord_1292330
  simp only [CollatzResearch.WordTrace]
  refine ⟨11783786852029149309324611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31423431605411064824865629 11783786852029149309324611)
  ·
    refine ⟨17675680278043723963986917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11783786852029149309324611 17675680278043723963986917)
    ·
      refine ⟨3314190052133198243247547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17675680278043723963986917 3314190052133198243247547)
      ·
        refine ⟨4971285078199797364871321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3314190052133198243247547 4971285078199797364871321)
        ·
          refine ⟨3728463808649848023653491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4971285078199797364871321 3728463808649848023653491)
          ·
            refine ⟨5592695712974772035480237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3728463808649848023653491 5592695712974772035480237)
            ·
              refine ⟨2097260892365539513305089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5592695712974772035480237 2097260892365539513305089)
              ·
                refine ⟨1572945669274154634978817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2097260892365539513305089 1572945669274154634978817)
                ·
                  refine ⟨1179709251955615976234113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1572945669274154634978817 1179709251955615976234113)
                  ·
                    refine ⟨884781938966711982175585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1179709251955615976234113 884781938966711982175585)
                    ·
                      refine ⟨663586454225033986631689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 884781938966711982175585 663586454225033986631689)
                      ·
                        rfl

theorem cell23_1292330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_1292330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292330 prefixEnd_1292330 := by exact prefixLift 1292330
  have htrace : WordTrace (prefixWord ++ tailWord_1292330) baseStart_1292330 baseEnd_1292330 := by
    simpa [prefixWord, tailWord_1292330, baseEnd_1292330] using wordTrace_append hprefix tailTrace_1292330
  have hstable : (prefixWord ++ tailWord_1292330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292330).length < 2 ^ (prefixWord ++ tailWord_1292330).sum := by decide
  have hdescent : baseEnd_1292330 < baseStart_1292330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292339 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 1, 7, 2]
def baseStart_1292339 : Nat := 118140960795 + 1292339 * 2 ^ 59
def prefixEnd_1292339 : Nat := 4983230072969 + 3 ^ 40 * 1292339 * 2
def baseEnd_1292339 : Nat := 663591075550924451419147

theorem tailTrace_1292339 : CollatzResearch.WordTrace tailWord_1292339 prefixEnd_1292339 663591075550924451419147 := by
  unfold tailWord_1292339
  simp only [CollatzResearch.WordTrace]
  refine ⟨47135475665083991774376071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31423650443389327849584047 47135475665083991774376071)
  ·
    refine ⟨70703213497625987661564107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47135475665083991774376071 70703213497625987661564107)
    ·
      refine ⟨106054820246438981492346161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70703213497625987661564107 106054820246438981492346161)
      ·
        refine ⟨79541115184829236119259621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106054820246438981492346161 79541115184829236119259621)
        ·
          refine ⟨14913959097155481772361179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79541115184829236119259621 14913959097155481772361179)
          ·
            refine ⟨22370938645733222658541769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14913959097155481772361179 22370938645733222658541769)
            ·
              refine ⟨16778203984299916993906327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22370938645733222658541769 16778203984299916993906327)
              ·
                refine ⟨25167305976449875490859491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16778203984299916993906327 25167305976449875490859491)
                ·
                  refine ⟨37750958964674813236289237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25167305976449875490859491 37750958964674813236289237)
                  ·
                    refine ⟨884788100734565935225529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37750958964674813236289237 884788100734565935225529)
                    ·
                      refine ⟨663591075550924451419147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 884788100734565935225529 663591075550924451419147)
                      ·
                        rfl

theorem cell23_1292339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 7, 2].length) (baseStart_1292339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292339 prefixEnd_1292339 := by exact prefixLift 1292339
  have htrace : WordTrace (prefixWord ++ tailWord_1292339) baseStart_1292339 baseEnd_1292339 := by
    simpa [prefixWord, tailWord_1292339, baseEnd_1292339] using wordTrace_append hprefix tailTrace_1292339
  have hstable : (prefixWord ++ tailWord_1292339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292339).length < 2 ^ (prefixWord ++ tailWord_1292339).sum := by decide
  have hdescent : baseEnd_1292339 < baseStart_1292339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292362 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 1, 10]
def baseStart_1292362 : Nat := 118140960795 + 1292362 * 2 ^ 59
def prefixEnd_1292362 : Nat := 4983230072969 + 3 ^ 40 * 1292362 * 2
def baseEnd_1292362 : Nat := 221200961868659287143847

theorem tailTrace_1292362 : CollatzResearch.WordTrace tailWord_1292362 prefixEnd_1292362 221200961868659287143847 := by
  unfold tailWord_1292362
  simp only [CollatzResearch.WordTrace]
  refine ⟨11784078636000166675615835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31424209696000444468308893 11784078636000166675615835)
  ·
    refine ⟨17676117954000250013423753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11784078636000166675615835 17676117954000250013423753)
    ·
      refine ⟨13257088465500187510067815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17676117954000250013423753 13257088465500187510067815)
      ·
        refine ⟨19885632698250281265101723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13257088465500187510067815 19885632698250281265101723)
        ·
          refine ⟨29828449047375421897652585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19885632698250281265101723 29828449047375421897652585)
          ·
            refine ⟨22371336785531566423239439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29828449047375421897652585 22371336785531566423239439)
            ·
              refine ⟨33557005178297349634859159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22371336785531566423239439 33557005178297349634859159)
              ·
                refine ⟨50335507767446024452288739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33557005178297349634859159 50335507767446024452288739)
                ·
                  refine ⟨75503261651169036678433109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50335507767446024452288739 75503261651169036678433109)
                  ·
                    refine ⟨221200961868659287143847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 75503261651169036678433109 221200961868659287143847)
                    ·
                      rfl

theorem cell23_1292362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_1292362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292362 prefixEnd_1292362 := by exact prefixLift 1292362
  have htrace : WordTrace (prefixWord ++ tailWord_1292362) baseStart_1292362 baseEnd_1292362 := by
    simpa [prefixWord, tailWord_1292362, baseEnd_1292362] using wordTrace_append hprefix tailTrace_1292362
  have hstable : (prefixWord ++ tailWord_1292362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292362).length < 2 ^ (prefixWord ++ tailWord_1292362).sum := by decide
  have hdescent : baseEnd_1292362 < baseStart_1292362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292369 : List Nat := [1, 2, 2, 1, 3, 1, 1, 5, 2, 1, 4]
def baseStart_1292369 : Nat := 118140960795 + 1292369 * 2 ^ 59
def prefixEnd_1292369 : Nat := 4983230072969 + 3 ^ 40 * 1292369 * 2
def baseEnd_1292369 : Nat := 663606479970559334044009

theorem tailTrace_1292369 : CollatzResearch.WordTrace tailWord_1292369 prefixEnd_1292369 663606479970559334044009 := by
  unfold tailWord_1292369
  simp only [CollatzResearch.WordTrace]
  refine ⟨47136569854975306897968161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31424379903316871265312107 47136569854975306897968161)
  ·
    refine ⟨35352427391231480173476121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47136569854975306897968161 35352427391231480173476121)
    ·
      refine ⟨26514320543423610130107091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35352427391231480173476121 26514320543423610130107091)
      ·
        refine ⟨39771480815135415195160637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26514320543423610130107091 39771480815135415195160637)
        ·
          refine ⟨14914305305675780698185239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39771480815135415195160637 14914305305675780698185239)
          ·
            refine ⟨22371457958513671047277859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14914305305675780698185239 22371457958513671047277859)
            ·
              refine ⟨33557186937770506570916789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22371457958513671047277859 33557186937770506570916789)
              ·
                refine ⟨3145986275415984991023449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33557186937770506570916789 3145986275415984991023449)
                ·
                  refine ⟨2359489706561988743267587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3145986275415984991023449 2359489706561988743267587)
                  ·
                    refine ⟨3539234559842983114901381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2359489706561988743267587 3539234559842983114901381)
                    ·
                      refine ⟨663606479970559334044009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3539234559842983114901381 663606479970559334044009)
                      ·
                        rfl

theorem cell23_1292369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_1292369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292369 prefixEnd_1292369 := by exact prefixLift 1292369
  have htrace : WordTrace (prefixWord ++ tailWord_1292369) baseStart_1292369 baseEnd_1292369 := by
    simpa [prefixWord, tailWord_1292369, baseEnd_1292369] using wordTrace_append hprefix tailTrace_1292369
  have hstable : (prefixWord ++ tailWord_1292369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292369).length < 2 ^ (prefixWord ++ tailWord_1292369).sum := by decide
  have hdescent : baseEnd_1292369 < baseStart_1292369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292370 : List Nat := [3, 2, 2, 1, 5, 1, 1, 3, 5]
def baseStart_1292370 : Nat := 118140960795 + 1292370 * 2 ^ 59
def prefixEnd_1292370 : Nat := 4983230072969 + 3 ^ 40 * 1292370 * 2
def baseEnd_1292370 : Nat := 73734110383468203347945

theorem tailTrace_1292370 : CollatzResearch.WordTrace tailWord_1292370 prefixEnd_1292370 73734110383468203347945 := by
  unfold tailWord_1292370
  simp only [CollatzResearch.WordTrace]
  refine ⟨11784151581992921017188641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31424404218647789379169709 11784151581992921017188641)
  ·
    refine ⟨8838113686494690762891481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11784151581992921017188641 8838113686494690762891481)
    ·
      refine ⟨6628585264871018072168611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8838113686494690762891481 6628585264871018072168611)
      ·
        refine ⟨9942877897306527108252917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6628585264871018072168611 9942877897306527108252917)
        ·
          refine ⟨932144802872486916398711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9942877897306527108252917 932144802872486916398711)
          ·
            refine ⟨1398217204308730374598067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 932144802872486916398711 1398217204308730374598067)
            ·
              refine ⟨2097325806463095561897101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1398217204308730374598067 2097325806463095561897101)
              ·
                refine ⟨786497177423660835711413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2097325806463095561897101 786497177423660835711413)
                ·
                  refine ⟨73734110383468203347945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 786497177423660835711413 73734110383468203347945)
                  ·
                    rfl

theorem cell23_1292370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3, 5].length) (baseStart_1292370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292370 prefixEnd_1292370 := by exact prefixLift 1292370
  have htrace : WordTrace (prefixWord ++ tailWord_1292370) baseStart_1292370 baseEnd_1292370 := by
    simpa [prefixWord, tailWord_1292370, baseEnd_1292370] using wordTrace_append hprefix tailTrace_1292370
  have hstable : (prefixWord ++ tailWord_1292370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292370).length < 2 ^ (prefixWord ++ tailWord_1292370).sum := by decide
  have hdescent : baseEnd_1292370 < baseStart_1292370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292396 : List Nat := [2, 2, 1, 1, 3, 3, 3, 1, 3, 4]
def baseStart_1292396 : Nat := 118140960795 + 1292396 * 2 ^ 59
def prefixEnd_1292396 : Nat := 4983230072969 + 3 ^ 40 * 1292396 * 2
def baseEnd_1292396 : Nat := 221206781316076909468795

theorem tailTrace_1292396 : CollatzResearch.WordTrace tailWord_1292396 prefixEnd_1292396 221206781316076909468795 := by
  unfold tailWord_1292396
  simp only [CollatzResearch.WordTrace]
  refine ⟨23568777312938745254600521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31425036417251660339467361 23568777312938745254600521)
  ·
    refine ⟨17676582984704058940950391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23568777312938745254600521 17676582984704058940950391)
    ·
      refine ⟨26514874477056088411425587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17676582984704058940950391 26514874477056088411425587)
      ·
        refine ⟨39772311715584132617138381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26514874477056088411425587 39772311715584132617138381)
        ·
          refine ⟨14914616893344049731426893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39772311715584132617138381 14914616893344049731426893)
          ·
            refine ⟨5592981335004018649285085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14914616893344049731426893 5592981335004018649285085)
            ·
              refine ⟨2097368000626506993481907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5592981335004018649285085 2097368000626506993481907)
              ·
                refine ⟨3146052000939760490222861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2097368000626506993481907 3146052000939760490222861)
                ·
                  refine ⟨1179769500352410183833573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3146052000939760490222861 1179769500352410183833573)
                  ·
                    refine ⟨221206781316076909468795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1179769500352410183833573 221206781316076909468795)
                    ·
                      rfl

theorem cell23_1292396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 4].length) (baseStart_1292396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292396 prefixEnd_1292396 := by exact prefixLift 1292396
  have htrace : WordTrace (prefixWord ++ tailWord_1292396) baseStart_1292396 baseEnd_1292396 := by
    simpa [prefixWord, tailWord_1292396, baseEnd_1292396] using wordTrace_append hprefix tailTrace_1292396
  have hstable : (prefixWord ++ tailWord_1292396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292396).length < 2 ^ (prefixWord ++ tailWord_1292396).sum := by decide
  have hdescent : baseEnd_1292396 < baseStart_1292396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292438 : List Nat := [5, 3, 2, 1, 2, 1, 2, 2, 5]
def baseStart_1292438 : Nat := 118140960795 + 1292438 * 2 ^ 59
def prefixEnd_1292438 : Nat := 4983230072969 + 3 ^ 40 * 1292438 * 2
def baseEnd_1292438 : Nat := 73737990015079951564577

theorem tailTrace_1292438 : CollatzResearch.WordTrace tailWord_1292438 prefixEnd_1292438 73737990015079951564577 := by
  unfold tailWord_1292438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2946192905732833230139373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31426057661150221121486645 2946192905732833230139373)
  ·
    refine ⟨1104822339649812461302265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2946192905732833230139373 1104822339649812461302265)
    ·
      refine ⟨828616754737359345976699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1104822339649812461302265 828616754737359345976699)
      ·
        refine ⟨1242925132106039018965049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 828616754737359345976699 1242925132106039018965049)
        ·
          refine ⟨932193849079529264223787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1242925132106039018965049 932193849079529264223787)
          ·
            refine ⟨1398290773619293896335681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 932193849079529264223787 1398290773619293896335681)
            ·
              refine ⟨1048718080214470422251761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1398290773619293896335681 1048718080214470422251761)
              ·
                refine ⟨786538560160852816688821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1048718080214470422251761 786538560160852816688821)
                ·
                  refine ⟨73737990015079951564577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 786538560160852816688821 73737990015079951564577)
                  ·
                    rfl

theorem cell23_1292438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_1292438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292438 prefixEnd_1292438 := by exact prefixLift 1292438
  have htrace : WordTrace (prefixWord ++ tailWord_1292438) baseStart_1292438 baseEnd_1292438 := by
    simpa [prefixWord, tailWord_1292438, baseEnd_1292438] using wordTrace_append hprefix tailTrace_1292438
  have hstable : (prefixWord ++ tailWord_1292438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292438).length < 2 ^ (prefixWord ++ tailWord_1292438).sum := by decide
  have hdescent : baseEnd_1292438 < baseStart_1292438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292447 : List Nat := [1, 1, 2, 6, 1, 3, 2, 2, 1, 4]
def baseStart_1292447 : Nat := 118140960795 + 1292447 * 2 ^ 59
def prefixEnd_1292447 : Nat := 4983230072969 + 3 ^ 40 * 1292447 * 2
def baseEnd_1292447 : Nat := 221215510487203342956217

theorem tailTrace_1292447 : CollatzResearch.WordTrace tailWord_1292447 prefixEnd_1292447 221215510487203342956217 := by
  unfold tailWord_1292447
  simp only [CollatzResearch.WordTrace]
  refine ⟨47139414748692726219307595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31426276499128484146205063 47139414748692726219307595)
  ·
    refine ⟨70709122123039089328961393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47139414748692726219307595 70709122123039089328961393)
    ·
      refine ⟨53031841592279316996721045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70709122123039089328961393 53031841592279316996721045)
      ·
        refine ⟨2485867574638092984221299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 53031841592279316996721045 2485867574638092984221299)
        ·
          refine ⟨3728801361957139476331949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2485867574638092984221299 3728801361957139476331949)
          ·
            refine ⟨1398300510733927303624481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3728801361957139476331949 1398300510733927303624481)
            ·
              refine ⟨1048725383050445477718361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1398300510733927303624481 1048725383050445477718361)
              ·
                refine ⟨786544037287834108288771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1048725383050445477718361 786544037287834108288771)
                ·
                  refine ⟨1179816055931751162433157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 786544037287834108288771 1179816055931751162433157)
                  ·
                    refine ⟨221215510487203342956217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1179816055931751162433157 221215510487203342956217)
                    ·
                      rfl

theorem cell23_1292447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2, 1, 4].length) (baseStart_1292447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292447 prefixEnd_1292447 := by exact prefixLift 1292447
  have htrace : WordTrace (prefixWord ++ tailWord_1292447) baseStart_1292447 baseEnd_1292447 := by
    simpa [prefixWord, tailWord_1292447, baseEnd_1292447] using wordTrace_append hprefix tailTrace_1292447
  have hstable : (prefixWord ++ tailWord_1292447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292447).length < 2 ^ (prefixWord ++ tailWord_1292447).sum := by decide
  have hdescent : baseEnd_1292447 < baseStart_1292447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292480 : List Nat := [2, 1, 1, 2, 5, 3, 1, 1, 2, 3, 2]
def baseStart_1292480 : Nat := 118140960795 + 1292480 * 2 ^ 59
def prefixEnd_1292480 : Nat := 4983230072969 + 3 ^ 40 * 1292480 * 2
def baseEnd_1292480 : Nat := 663663476323208399755999

theorem tailTrace_1292480 : CollatzResearch.WordTrace tailWord_1292480 prefixEnd_1292480 663663476323208399755999 := by
  unfold tailWord_1292480
  simp only [CollatzResearch.WordTrace]
  refine ⟨23570309178786586427629447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31427078905048781903505929 23570309178786586427629447)
  ·
    refine ⟨35355463768179879641444171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23570309178786586427629447 35355463768179879641444171)
    ·
      refine ⟨53033195652269819462166257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35355463768179879641444171 53033195652269819462166257)
      ·
        refine ⟨39774896739202364596624693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53033195652269819462166257 39774896739202364596624693)
        ·
          refine ⟨3728896569300221680933565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39774896739202364596624693 3728896569300221680933565)
          ·
            refine ⟨1398336213487583130350087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3728896569300221680933565 1398336213487583130350087)
            ·
              refine ⟨2097504320231374695525131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1398336213487583130350087 2097504320231374695525131)
              ·
                refine ⟨3146256480347062043287697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2097504320231374695525131 3146256480347062043287697)
                ·
                  refine ⟨2359692360260296532465773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3146256480347062043287697 2359692360260296532465773)
                  ·
                    refine ⟨884884635097611199674665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2359692360260296532465773 884884635097611199674665)
                    ·
                      refine ⟨663663476323208399755999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 884884635097611199674665 663663476323208399755999)
                      ·
                        rfl

theorem cell23_1292480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 2, 3, 2].length) (baseStart_1292480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292480 prefixEnd_1292480 := by exact prefixLift 1292480
  have htrace : WordTrace (prefixWord ++ tailWord_1292480) baseStart_1292480 baseEnd_1292480 := by
    simpa [prefixWord, tailWord_1292480, baseEnd_1292480] using wordTrace_append hprefix tailTrace_1292480
  have hstable : (prefixWord ++ tailWord_1292480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292480).length < 2 ^ (prefixWord ++ tailWord_1292480).sum := by decide
  have hdescent : baseEnd_1292480 < baseStart_1292480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292489 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 3, 2, 4]
def baseStart_1292489 : Nat := 118140960795 + 1292489 * 2 ^ 59
def prefixEnd_1292489 : Nat := 4983230072969 + 3 ^ 40 * 1292489 * 2
def baseEnd_1292489 : Nat := 663668097649098864543457

theorem tailTrace_1292489 : CollatzResearch.WordTrace tailWord_1292489 prefixEnd_1292489 663668097649098864543457 := by
  unfold tailWord_1292489
  simp only [CollatzResearch.WordTrace]
  refine ⟨47140946614540567392336521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31427297743027044928224347 47140946614540567392336521)
  ·
    refine ⟨35355709960905425544252391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47140946614540567392336521 35355709960905425544252391)
    ·
      refine ⟨53033564941358138316378587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35355709960905425544252391 53033564941358138316378587)
      ·
        refine ⟨79550347412037207474567881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53033564941358138316378587 79550347412037207474567881)
        ·
          refine ⟨59662760559027905605925911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79550347412037207474567881 59662760559027905605925911)
          ·
            refine ⟨89494140838541858408888867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59662760559027905605925911 89494140838541858408888867)
            ·
              refine ⟨134241211257812787613333301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89494140838541858408888867 134241211257812787613333301)
              ·
                refine ⟨12585113555419948838749997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 134241211257812787613333301 12585113555419948838749997)
                ·
                  refine ⟨4719417583282480814531249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12585113555419948838749997 4719417583282480814531249)
                  ·
                    refine ⟨3539563187461860610898437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4719417583282480814531249 3539563187461860610898437)
                    ·
                      refine ⟨663668097649098864543457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3539563187461860610898437 663668097649098864543457)
                      ·
                        rfl

theorem cell23_1292489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 2, 4].length) (baseStart_1292489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292489 prefixEnd_1292489 := by exact prefixLift 1292489
  have htrace : WordTrace (prefixWord ++ tailWord_1292489) baseStart_1292489 baseEnd_1292489 := by
    simpa [prefixWord, tailWord_1292489, baseEnd_1292489] using wordTrace_append hprefix tailTrace_1292489
  have hstable : (prefixWord ++ tailWord_1292489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292489).length < 2 ^ (prefixWord ++ tailWord_1292489).sum := by decide
  have hdescent : baseEnd_1292489 < baseStart_1292489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292520 : List Nat := [2, 1, 4, 1, 2, 3, 3, 1, 2, 4]
def baseStart_1292520 : Nat := 118140960795 + 1292520 * 2 ^ 59
def prefixEnd_1292520 : Nat := 4983230072969 + 3 ^ 40 * 1292520 * 2
def baseEnd_1292520 : Nat := 221228005183129414418605

theorem tailTrace_1292520 : CollatzResearch.WordTrace tailWord_1292520 prefixEnd_1292520 221228005183129414418605 := by
  unfold tailWord_1292520
  simp only [CollatzResearch.WordTrace]
  refine ⟨23571038638714129843357507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31428051518285506457810009 23571038638714129843357507)
  ·
    refine ⟨35356557958071194765036261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23571038638714129843357507 35356557958071194765036261)
    ·
      refine ⟨6629354617138349018444299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35356557958071194765036261 6629354617138349018444299)
      ·
        refine ⟨9944031925707523527666449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6629354617138349018444299 9944031925707523527666449)
        ·
          refine ⟨7458023944280642645749837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9944031925707523527666449 7458023944280642645749837)
          ·
            refine ⟨2796758979105240992156189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7458023944280642645749837 2796758979105240992156189)
            ·
              refine ⟨1048784617164465372058571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2796758979105240992156189 1048784617164465372058571)
              ·
                refine ⟨1573176925746698058087857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1048784617164465372058571 1573176925746698058087857)
                ·
                  refine ⟨1179882694310023543565893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1573176925746698058087857 1179882694310023543565893)
                  ·
                    refine ⟨221228005183129414418605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1179882694310023543565893 221228005183129414418605)
                    ·
                      rfl

theorem cell23_1292520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_1292520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292520 prefixEnd_1292520 := by exact prefixLift 1292520
  have htrace : WordTrace (prefixWord ++ tailWord_1292520) baseStart_1292520 baseEnd_1292520 := by
    simpa [prefixWord, tailWord_1292520, baseEnd_1292520] using wordTrace_append hprefix tailTrace_1292520
  have hstable : (prefixWord ++ tailWord_1292520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292520).length < 2 ^ (prefixWord ++ tailWord_1292520).sum := by decide
  have hdescent : baseEnd_1292520 < baseStart_1292520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292529 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 2, 7]
def baseStart_1292529 : Nat := 118140960795 + 1292529 * 2 ^ 59
def prefixEnd_1292529 : Nat := 4983230072969 + 3 ^ 40 * 1292529 * 2
def baseEnd_1292529 : Nat := 221229545625092902681091

theorem tailTrace_1292529 : CollatzResearch.WordTrace tailWord_1292529 prefixEnd_1292529 221229545625092902681091 := by
  unfold tailWord_1292529
  simp only [CollatzResearch.WordTrace]
  refine ⟨47142405534395654223792641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31428270356263769482528427 47142405534395654223792641)
  ·
    refine ⟨35356804150796740667844481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47142405534395654223792641 35356804150796740667844481)
    ·
      refine ⟨26517603113097555500883361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35356804150796740667844481 26517603113097555500883361)
      ·
        refine ⟨19888202334823166625662521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26517603113097555500883361 19888202334823166625662521)
        ·
          refine ⟨14916151751117374969246891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19888202334823166625662521 14916151751117374969246891)
          ·
            refine ⟨22374227626676062453870337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14916151751117374969246891 22374227626676062453870337)
            ·
              refine ⟨16780670720007046840402753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22374227626676062453870337 16780670720007046840402753)
              ·
                refine ⟨12585503040005285130302065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16780670720007046840402753 12585503040005285130302065)
                ·
                  refine ⟨9439127280003963847726549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12585503040005285130302065 9439127280003963847726549)
                  ·
                    refine ⟨221229545625092902681091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9439127280003963847726549 221229545625092902681091)
                    ·
                      rfl

theorem cell23_1292529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 7].length) (baseStart_1292529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292529 prefixEnd_1292529 := by exact prefixLift 1292529
  have htrace : WordTrace (prefixWord ++ tailWord_1292529) baseStart_1292529 baseEnd_1292529 := by
    simpa [prefixWord, tailWord_1292529, baseEnd_1292529] using wordTrace_append hprefix tailTrace_1292529
  have hstable : (prefixWord ++ tailWord_1292529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292529).length < 2 ^ (prefixWord ++ tailWord_1292529).sum := by decide
  have hdescent : baseEnd_1292529 < baseStart_1292529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292530 : List Nat := [3, 2, 1, 3, 2, 2, 2, 2, 1, 2, 3]
def baseStart_1292530 : Nat := 118140960795 + 1292530 * 2 ^ 59
def prefixEnd_1292530 : Nat := 4983230072969 + 3 ^ 40 * 1292530 * 2
def baseEnd_1292530 : Nat := 663689150355933204130769

theorem tailTrace_1292530 : CollatzResearch.WordTrace tailWord_1292530 prefixEnd_1292530 663689150355933204130769 := by
  unfold tailWord_1292530
  simp only [CollatzResearch.WordTrace]
  refine ⟨11785610501848007848644761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31428294671594687596386029 11785610501848007848644761)
  ·
    refine ⟨8839207876386005886483571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11785610501848007848644761 8839207876386005886483571)
    ·
      refine ⟨13258811814579008829725357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8839207876386005886483571 13258811814579008829725357)
      ·
        refine ⟨4972054430467128311147009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13258811814579008829725357 4972054430467128311147009)
        ·
          refine ⟨3729040822850346233360257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4972054430467128311147009 3729040822850346233360257)
          ·
            refine ⟨2796780617137759675020193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3729040822850346233360257 2796780617137759675020193)
            ·
              refine ⟨2097585462853319756265145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2796780617137759675020193 2097585462853319756265145)
              ·
                refine ⟨1573189097139989817198859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2097585462853319756265145 1573189097139989817198859)
                ·
                  refine ⟨2359783645709984725798289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1573189097139989817198859 2359783645709984725798289)
                  ·
                    refine ⟨1769837734282488544348717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2359783645709984725798289 1769837734282488544348717)
                    ·
                      refine ⟨663689150355933204130769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1769837734282488544348717 663689150355933204130769)
                      ·
                        rfl

theorem cell23_1292530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_1292530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292530 prefixEnd_1292530 := by exact prefixLift 1292530
  have htrace : WordTrace (prefixWord ++ tailWord_1292530) baseStart_1292530 baseEnd_1292530 := by
    simpa [prefixWord, tailWord_1292530, baseEnd_1292530] using wordTrace_append hprefix tailTrace_1292530
  have hstable : (prefixWord ++ tailWord_1292530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292530).length < 2 ^ (prefixWord ++ tailWord_1292530).sum := by decide
  have hdescent : baseEnd_1292530 < baseStart_1292530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292536 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 2, 7, 2]
def baseStart_1292536 : Nat := 118140960795 + 1292536 * 2 ^ 59
def prefixEnd_1292536 : Nat := 4983230072969 + 3 ^ 40 * 1292536 * 2
def baseEnd_1292536 : Nat := 663692231239860180655741

theorem tailTrace_1292536 : CollatzResearch.WordTrace tailWord_1292536 prefixEnd_1292536 663692231239860180655741 := by
  unfold tailWord_1292536
  simp only [CollatzResearch.WordTrace]
  refine ⟨23571330422685147209648731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31428440563580196279531641 23571330422685147209648731)
  ·
    refine ⟨35356995634027720814473097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23571330422685147209648731 35356995634027720814473097)
    ·
      refine ⟨26517746725520790610854823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35356995634027720814473097 26517746725520790610854823)
      ·
        refine ⟨39776620088281185916282235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26517746725520790610854823 39776620088281185916282235)
        ·
          refine ⟨59664930132421778874423353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39776620088281185916282235 59664930132421778874423353)
          ·
            refine ⟨44748697599316334155817515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59664930132421778874423353 44748697599316334155817515)
            ·
              refine ⟨67123046398974501233726273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44748697599316334155817515 67123046398974501233726273)
              ·
                refine ⟨50342284799230875925294705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67123046398974501233726273 50342284799230875925294705)
                ·
                  refine ⟨37756713599423156943971029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50342284799230875925294705 37756713599423156943971029)
                  ·
                    refine ⟨884922974986480240874321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37756713599423156943971029 884922974986480240874321)
                    ·
                      refine ⟨663692231239860180655741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 884922974986480240874321 663692231239860180655741)
                      ·
                        rfl

theorem cell23_1292536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 7, 2].length) (baseStart_1292536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292536 prefixEnd_1292536 := by exact prefixLift 1292536
  have htrace : WordTrace (prefixWord ++ tailWord_1292536) baseStart_1292536 baseEnd_1292536 := by
    simpa [prefixWord, tailWord_1292536, baseEnd_1292536] using wordTrace_append hprefix tailTrace_1292536
  have hstable : (prefixWord ++ tailWord_1292536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292536).length < 2 ^ (prefixWord ++ tailWord_1292536).sum := by decide
  have hdescent : baseEnd_1292536 < baseStart_1292536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292559 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 4, 6]
def baseStart_1292559 : Nat := 118140960795 + 1292559 * 2 ^ 59
def prefixEnd_1292559 : Nat := 4983230072969 + 3 ^ 40 * 1292559 * 2
def baseEnd_1292559 : Nat := 221234680431637863556045

theorem tailTrace_1292559 : CollatzResearch.WordTrace tailWord_1292559 prefixEnd_1292559 221234680431637863556045 := by
  unfold tailWord_1292559
  simp only [CollatzResearch.WordTrace]
  refine ⟨47143499724286969347384731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31428999816191312898256487 47143499724286969347384731)
  ·
    refine ⟨70715249586430454021077097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47143499724286969347384731 70715249586430454021077097)
    ·
      refine ⟨53036437189822840515807823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70715249586430454021077097 53036437189822840515807823)
      ·
        refine ⟨79554655784734260773711735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53036437189822840515807823 79554655784734260773711735)
        ·
          refine ⟨119331983677101391160567603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79554655784734260773711735 119331983677101391160567603)
          ·
            refine ⟨178997975515652086740851405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119331983677101391160567603 178997975515652086740851405)
            ·
              refine ⟨67124240818369532527819277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178997975515652086740851405 67124240818369532527819277)
              ·
                refine ⟨25171590306888574697932229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67124240818369532527819277 25171590306888574697932229)
                ·
                  refine ⟨4719673182541607755862293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25171590306888574697932229 4719673182541607755862293)
                  ·
                    refine ⟨221234680431637863556045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4719673182541607755862293 221234680431637863556045)
                    ·
                      rfl

theorem cell23_1292559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 6].length) (baseStart_1292559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292559 prefixEnd_1292559 := by exact prefixLift 1292559
  have htrace : WordTrace (prefixWord ++ tailWord_1292559) baseStart_1292559 baseEnd_1292559 := by
    simpa [prefixWord, tailWord_1292559, baseEnd_1292559] using wordTrace_append hprefix tailTrace_1292559
  have hstable : (prefixWord ++ tailWord_1292559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292559).length < 2 ^ (prefixWord ++ tailWord_1292559).sum := by decide
  have hdescent : baseEnd_1292559 < baseStart_1292559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292643 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 2, 5, 2]
def baseStart_1292643 : Nat := 118140960795 + 1292643 * 2 ^ 59
def prefixEnd_1292643 : Nat := 4983230072969 + 3 ^ 40 * 1292643 * 2
def baseEnd_1292643 : Nat := 663747173669891262017749

theorem tailTrace_1292643 : CollatzResearch.WordTrace tailWord_1292643 prefixEnd_1292643 663747173669891262017749 := by
  unfold tailWord_1292643
  simp only [CollatzResearch.WordTrace]
  refine ⟨47146563455982651693442583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31431042303988434462295055 47146563455982651693442583)
  ·
    refine ⟨70719845183973977540163875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47146563455982651693442583 70719845183973977540163875)
    ·
      refine ⟨106079767775960966310245813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70719845183973977540163875 106079767775960966310245813)
      ·
        refine ⟨9944978228996340591585545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106079767775960966310245813 9944978228996340591585545)
        ·
          refine ⟨7458733671747255443689159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9944978228996340591585545 7458733671747255443689159)
          ·
            refine ⟨11188100507620883165533739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7458733671747255443689159 11188100507620883165533739)
            ·
              refine ⟨16782150761431324748300609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11188100507620883165533739 16782150761431324748300609)
              ·
                refine ⟨12586613071073493561225457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16782150761431324748300609 12586613071073493561225457)
                ·
                  refine ⟨9439959803305120170919093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12586613071073493561225457 9439959803305120170919093)
                  ·
                    refine ⟨884996231559855016023665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9439959803305120170919093 884996231559855016023665)
                    ·
                      refine ⟨663747173669891262017749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 884996231559855016023665 663747173669891262017749)
                      ·
                        rfl

theorem cell23_1292643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_1292643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292643 prefixEnd_1292643 := by exact prefixLift 1292643
  have htrace : WordTrace (prefixWord ++ tailWord_1292643) baseStart_1292643 baseEnd_1292643 := by
    simpa [prefixWord, tailWord_1292643, baseEnd_1292643] using wordTrace_append hprefix tailTrace_1292643
  have hstable : (prefixWord ++ tailWord_1292643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292643).length < 2 ^ (prefixWord ++ tailWord_1292643).sum := by decide
  have hdescent : baseEnd_1292643 < baseStart_1292643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292683 : List Nat := [1, 1, 1, 1, 4, 4, 1, 3, 3, 4]
def baseStart_1292683 : Nat := 118140960795 + 1292683 * 2 ^ 59
def prefixEnd_1292683 : Nat := 4983230072969 + 3 ^ 40 * 1292683 * 2
def baseEnd_1292683 : Nat := 221255904298690368505855

theorem tailTrace_1292683 : CollatzResearch.WordTrace tailWord_1292683 prefixEnd_1292683 221255904298690368505855 := by
  unfold tailWord_1292683
  simp only [CollatzResearch.WordTrace]
  refine ⟨47148022375837738524898703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31432014917225159016599135 47148022375837738524898703)
  ·
    refine ⟨70722033563756607787348055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47148022375837738524898703 70722033563756607787348055)
    ·
      refine ⟨106083050345634911681022083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70722033563756607787348055 106083050345634911681022083)
      ·
        refine ⟨159124575518452367521533125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106083050345634911681022083 159124575518452367521533125)
        ·
          refine ⟨29835857909709818910287461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159124575518452367521533125 29835857909709818910287461)
          ·
            refine ⟨5594223358070591045678899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29835857909709818910287461 5594223358070591045678899)
            ·
              refine ⟨8391335037105886568518349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5594223358070591045678899 8391335037105886568518349)
              ·
                refine ⟨3146750638914707463194381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8391335037105886568518349 3146750638914707463194381)
                ·
                  refine ⟨1180031489593015298697893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3146750638914707463194381 1180031489593015298697893)
                  ·
                    refine ⟨221255904298690368505855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1180031489593015298697893 221255904298690368505855)
                    ·
                      rfl

theorem cell23_1292683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3, 4].length) (baseStart_1292683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292683 prefixEnd_1292683 := by exact prefixLift 1292683
  have htrace : WordTrace (prefixWord ++ tailWord_1292683) baseStart_1292683 baseEnd_1292683 := by
    simpa [prefixWord, tailWord_1292683, baseEnd_1292683] using wordTrace_append hprefix tailTrace_1292683
  have hstable : (prefixWord ++ tailWord_1292683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292683).length < 2 ^ (prefixWord ++ tailWord_1292683).sum := by decide
  have hdescent : baseEnd_1292683 < baseStart_1292683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292724 : List Nat := [2, 5, 2, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_1292724 : Nat := 118140960795 + 1292724 * 2 ^ 59
def prefixEnd_1292724 : Nat := 4983230072969 + 3 ^ 40 * 1292724 * 2
def baseEnd_1292724 : Nat := 663788765602905445104877

theorem tailTrace_1292724 : CollatzResearch.WordTrace tailWord_1292724 prefixEnd_1292724 663788765602905445104877 := by
  unfold tailWord_1292724
  simp only [CollatzResearch.WordTrace]
  refine ⟨23574758884344601263570613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31433011845792801684760817 23574758884344601263570613)
  ·
    refine ⟨2210133645407306368459745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23574758884344601263570613 2210133645407306368459745)
    ·
      refine ⟨1657600234055479776344809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2210133645407306368459745 1657600234055479776344809)
      ·
        refine ⟨1243200175541609832258607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1657600234055479776344809 1243200175541609832258607)
        ·
          refine ⟨1864800263312414748387911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1243200175541609832258607 1864800263312414748387911)
          ·
            refine ⟨2797200394968622122581867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1864800263312414748387911 2797200394968622122581867)
            ·
              refine ⟨4195800592452933183872801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2797200394968622122581867 4195800592452933183872801)
              ·
                refine ⟨3146850444339699887904601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4195800592452933183872801 3146850444339699887904601)
                ·
                  refine ⟨2360137833254774915928451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3146850444339699887904601 2360137833254774915928451)
                  ·
                    refine ⟨3540206749882162373892677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2360137833254774915928451 3540206749882162373892677)
                    ·
                      refine ⟨663788765602905445104877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3540206749882162373892677 663788765602905445104877)
                      ·
                        rfl

theorem cell23_1292724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_1292724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292724 prefixEnd_1292724 := by exact prefixLift 1292724
  have htrace : WordTrace (prefixWord ++ tailWord_1292724) baseStart_1292724 baseEnd_1292724 := by
    simpa [prefixWord, tailWord_1292724, baseEnd_1292724] using wordTrace_append hprefix tailTrace_1292724
  have hstable : (prefixWord ++ tailWord_1292724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292724).length < 2 ^ (prefixWord ++ tailWord_1292724).sum := by decide
  have hdescent : baseEnd_1292724 < baseStart_1292724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292736 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 7]
def baseStart_1292736 : Nat := 118140960795 + 1292736 * 2 ^ 59
def prefixEnd_1292736 : Nat := 4983230072969 + 3 ^ 40 * 1292736 * 2
def baseEnd_1292736 : Nat := 663794927370759398154821

theorem tailTrace_1292736 : CollatzResearch.WordTrace tailWord_1292736 prefixEnd_1292736 663794927370759398154821 := by
  unfold tailWord_1292736
  simp only [CollatzResearch.WordTrace]
  refine ⟨23574977722322864288289031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31433303629763819051052041 23574977722322864288289031)
  ·
    refine ⟨35362466583484296432433547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23574977722322864288289031 35362466583484296432433547)
    ·
      refine ⟨53043699875226444648650321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35362466583484296432433547 53043699875226444648650321)
      ·
        refine ⟨39782774906419833486487741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53043699875226444648650321 39782774906419833486487741)
        ·
          refine ⟨14918540589907437557432903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39782774906419833486487741 14918540589907437557432903)
          ·
            refine ⟨22377810884861156336149355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14918540589907437557432903 22377810884861156336149355)
            ·
              refine ⟨33566716327291734504224033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22377810884861156336149355 33566716327291734504224033)
              ·
                refine ⟨25175037245468800878168025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33566716327291734504224033 25175037245468800878168025)
                ·
                  refine ⟨18881277934101600658626019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25175037245468800878168025 18881277934101600658626019)
                  ·
                    refine ⟨28321916901152400987939029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18881277934101600658626019 28321916901152400987939029)
                    ·
                      refine ⟨663794927370759398154821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28321916901152400987939029 663794927370759398154821)
                      ·
                        rfl

theorem cell23_1292736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_1292736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292736 prefixEnd_1292736 := by exact prefixLift 1292736
  have htrace : WordTrace (prefixWord ++ tailWord_1292736) baseStart_1292736 baseEnd_1292736 := by
    simpa [prefixWord, tailWord_1292736, baseEnd_1292736] using wordTrace_append hprefix tailTrace_1292736
  have hstable : (prefixWord ++ tailWord_1292736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292736).length < 2 ^ (prefixWord ++ tailWord_1292736).sum := by decide
  have hdescent : baseEnd_1292736 < baseStart_1292736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292750 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2]
def baseStart_1292750 : Nat := 118140960795 + 1292750 * 2 ^ 59
def prefixEnd_1292750 : Nat := 4983230072969 + 3 ^ 40 * 1292750 * 2
def baseEnd_1292750 : Nat := 663802116099922343379757

theorem tailTrace_1292750 : CollatzResearch.WordTrace tailWord_1292750 prefixEnd_1292750 663802116099922343379757 := by
  unfold tailWord_1292750
  simp only [CollatzResearch.WordTrace]
  refine ⟨5893808258324376120948463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31433644044396672645058469 5893808258324376120948463)
  ·
    refine ⟨8840712387486564181422695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5893808258324376120948463 8840712387486564181422695)
    ·
      refine ⟨13261068581229846272134043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8840712387486564181422695 13261068581229846272134043)
      ·
        refine ⟨19891602871844769408201065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13261068581229846272134043 19891602871844769408201065)
        ·
          refine ⟨14918702153883577056150799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19891602871844769408201065 14918702153883577056150799)
          ·
            refine ⟨22378053230825365584226199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14918702153883577056150799 22378053230825365584226199)
            ·
              refine ⟨33567079846238048376339299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22378053230825365584226199 33567079846238048376339299)
              ·
                refine ⟨50350619769357072564508949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33567079846238048376339299 50350619769357072564508949)
                ·
                  refine ⟨2360185301688612776461357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50350619769357072564508949 2360185301688612776461357)
                  ·
                    refine ⟨885069488133229791173009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2360185301688612776461357 885069488133229791173009)
                    ·
                      refine ⟨663802116099922343379757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 885069488133229791173009 663802116099922343379757)
                      ·
                        rfl

theorem cell23_1292750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2].length) (baseStart_1292750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292750 prefixEnd_1292750 := by exact prefixLift 1292750
  have htrace : WordTrace (prefixWord ++ tailWord_1292750) baseStart_1292750 baseEnd_1292750 := by
    simpa [prefixWord, tailWord_1292750, baseEnd_1292750] using wordTrace_append hprefix tailTrace_1292750
  have hstable : (prefixWord ++ tailWord_1292750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292750).length < 2 ^ (prefixWord ++ tailWord_1292750).sum := by decide
  have hdescent : baseEnd_1292750 < baseStart_1292750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292767 : List Nat := [1, 1, 2, 3, 3, 3, 2, 1, 2, 3, 2]
def baseStart_1292767 : Nat := 118140960795 + 1292767 * 2 ^ 59
def prefixEnd_1292767 : Nat := 4983230072969 + 3 ^ 40 * 1292767 * 2
def baseEnd_1292767 : Nat := 663810845271048776867179

theorem tailTrace_1292767 : CollatzResearch.WordTrace tailWord_1292767 prefixEnd_1292767 663810845271048776867179 := by
  unfold tailWord_1292767
  simp only [CollatzResearch.WordTrace]
  refine ⟨47151086107533420870956555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31434057405022280580637703 47151086107533420870956555)
  ·
    refine ⟨70726629161300131306434833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47151086107533420870956555 70726629161300131306434833)
    ·
      refine ⟨53044971870975098479826125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70726629161300131306434833 53044971870975098479826125)
      ·
        refine ⟨19891864451615661929934797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53044971870975098479826125 19891864451615661929934797)
        ·
          refine ⟨7459449169355873223725549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19891864451615661929934797 7459449169355873223725549)
          ·
            refine ⟨2797293438508452458897081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7459449169355873223725549 2797293438508452458897081)
            ·
              refine ⟨2097970078881339344172811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2797293438508452458897081 2097970078881339344172811)
              ·
                refine ⟨3146955118322009016259217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2097970078881339344172811 3146955118322009016259217)
                ·
                  refine ⟨2360216338741506762194413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3146955118322009016259217 2360216338741506762194413)
                  ·
                    refine ⟨885081127028065035822905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2360216338741506762194413 885081127028065035822905)
                    ·
                      refine ⟨663810845271048776867179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 885081127028065035822905 663810845271048776867179)
                      ·
                        rfl

theorem cell23_1292767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 3, 2].length) (baseStart_1292767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292767 prefixEnd_1292767 := by exact prefixLift 1292767
  have htrace : WordTrace (prefixWord ++ tailWord_1292767) baseStart_1292767 baseEnd_1292767 := by
    simpa [prefixWord, tailWord_1292767, baseEnd_1292767] using wordTrace_append hprefix tailTrace_1292767
  have hstable : (prefixWord ++ tailWord_1292767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292767).length < 2 ^ (prefixWord ++ tailWord_1292767).sum := by decide
  have hdescent : baseEnd_1292767 < baseStart_1292767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292797 : List Nat := [1, 4, 1, 1, 1, 3, 2, 3, 3, 2, 2]
def baseStart_1292797 : Nat := 118140960795 + 1292797 * 2 ^ 59
def prefixEnd_1292797 : Nat := 4983230072969 + 3 ^ 40 * 1292797 * 2
def baseEnd_1292797 : Nat := 663826249690683659492041

theorem tailTrace_1292797 : CollatzResearch.WordTrace tailWord_1292797 prefixEnd_1292797 663826249690683659492041 := by
  unfold tailWord_1292797
  simp only [CollatzResearch.WordTrace]
  refine ⟨47152180297424735994548645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31434786864949823996365763 47152180297424735994548645)
  ·
    refine ⟨8841033805767137998977871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47152180297424735994548645 8841033805767137998977871)
    ·
      refine ⟨13261550708650706998466807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8841033805767137998977871 13261550708650706998466807)
      ·
        refine ⟨19892326062976060497700211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13261550708650706998466807 19892326062976060497700211)
        ·
          refine ⟨29838489094464090746550317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19892326062976060497700211 29838489094464090746550317)
          ·
            refine ⟨11189433410424034029956369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29838489094464090746550317 11189433410424034029956369)
            ·
              refine ⟨8392075057818025522467277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11189433410424034029956369 8392075057818025522467277)
              ·
                refine ⟨3147028146681759570925229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8392075057818025522467277 3147028146681759570925229)
                ·
                  refine ⟨1180135555005659839096961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3147028146681759570925229 1180135555005659839096961)
                  ·
                    refine ⟨885101666254244879322721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1180135555005659839096961 885101666254244879322721)
                    ·
                      refine ⟨663826249690683659492041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 885101666254244879322721 663826249690683659492041)
                      ·
                        rfl

theorem cell23_1292797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3, 2, 2].length) (baseStart_1292797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292797 prefixEnd_1292797 := by exact prefixLift 1292797
  have htrace : WordTrace (prefixWord ++ tailWord_1292797) baseStart_1292797 baseEnd_1292797 := by
    simpa [prefixWord, tailWord_1292797, baseEnd_1292797] using wordTrace_append hprefix tailTrace_1292797
  have hstable : (prefixWord ++ tailWord_1292797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292797).length < 2 ^ (prefixWord ++ tailWord_1292797).sum := by decide
  have hdescent : baseEnd_1292797 < baseStart_1292797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292810 : List Nat := [3, 1, 2, 2, 2, 1, 4, 1, 1, 2, 4]
def baseStart_1292810 : Nat := 118140960795 + 1292810 * 2 ^ 59
def prefixEnd_1292810 : Nat := 4983230072969 + 3 ^ 40 * 1292810 * 2
def baseEnd_1292810 : Nat := 663832924939192108629481

theorem tailTrace_1292810 : CollatzResearch.WordTrace tailWord_1292810 prefixEnd_1292810 663832924939192108629481 := by
  unfold tailWord_1292810
  simp only [CollatzResearch.WordTrace]
  refine ⟨11788163611594409803692971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31435102964251759476514589 11788163611594409803692971)
  ·
    refine ⟨17682245417391614705539457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11788163611594409803692971 17682245417391614705539457)
    ·
      refine ⟨13261684063043711029154593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17682245417391614705539457 13261684063043711029154593)
      ·
        refine ⟨9946263047282783271865945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13261684063043711029154593 9946263047282783271865945)
        ·
          refine ⟨7459697285462087453899459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9946263047282783271865945 7459697285462087453899459)
          ·
            refine ⟨11189545928193131180849189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7459697285462087453899459 11189545928193131180849189)
            ·
              refine ⟨2098039861536212096409223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11189545928193131180849189 2098039861536212096409223)
              ·
                refine ⟨3147059792304318144613835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2098039861536212096409223 3147059792304318144613835)
                ·
                  refine ⟨4720589688456477216920753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3147059792304318144613835 4720589688456477216920753)
                  ·
                    refine ⟨3540442266342357912690565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4720589688456477216920753 3540442266342357912690565)
                    ·
                      refine ⟨663832924939192108629481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3540442266342357912690565 663832924939192108629481)
                      ·
                        rfl

theorem cell23_1292810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_1292810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292810 prefixEnd_1292810 := by exact prefixLift 1292810
  have htrace : WordTrace (prefixWord ++ tailWord_1292810) baseStart_1292810 baseEnd_1292810 := by
    simpa [prefixWord, tailWord_1292810, baseEnd_1292810] using wordTrace_append hprefix tailTrace_1292810
  have hstable : (prefixWord ++ tailWord_1292810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292810).length < 2 ^ (prefixWord ++ tailWord_1292810).sum := by decide
  have hdescent : baseEnd_1292810 < baseStart_1292810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292814 : List Nat := [4, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2]
def baseStart_1292814 : Nat := 118140960795 + 1292814 * 2 ^ 59
def prefixEnd_1292814 : Nat := 4983230072969 + 3 ^ 40 * 1292814 * 2
def baseEnd_1292814 : Nat := 663834978861810092979463

theorem tailTrace_1292814 : CollatzResearch.WordTrace tailWord_1292814 prefixEnd_1292814 663834978861810092979463 := by
  unfold tailWord_1292814
  simp only [CollatzResearch.WordTrace]
  refine ⟨5894100042295393487239687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31435200225575431931944997 5894100042295393487239687)
  ·
    refine ⟨8841150063443090230859531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5894100042295393487239687 8841150063443090230859531)
    ·
      refine ⟨13261725095164635346289297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8841150063443090230859531 13261725095164635346289297)
      ·
        refine ⟨9946293821373476509716973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13261725095164635346289297 9946293821373476509716973)
        ·
          refine ⟨3729860183015053691143865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9946293821373476509716973 3729860183015053691143865)
          ·
            refine ⟨2797395137261290268357899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3729860183015053691143865 2797395137261290268357899)
            ·
              refine ⟨4196092705891935402536849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2797395137261290268357899 4196092705891935402536849)
              ·
                refine ⟨3147069529418951551902637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4196092705891935402536849 3147069529418951551902637)
                ·
                  refine ⟨1180151073532106831963489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3147069529418951551902637 1180151073532106831963489)
                  ·
                    refine ⟨885113305149080123972617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1180151073532106831963489 885113305149080123972617)
                    ·
                      refine ⟨663834978861810092979463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 885113305149080123972617 663834978861810092979463)
                      ·
                        rfl

theorem cell23_1292814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_1292814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292814 prefixEnd_1292814 := by exact prefixLift 1292814
  have htrace : WordTrace (prefixWord ++ tailWord_1292814) baseStart_1292814 baseEnd_1292814 := by
    simpa [prefixWord, tailWord_1292814, baseEnd_1292814] using wordTrace_append hprefix tailTrace_1292814
  have hstable : (prefixWord ++ tailWord_1292814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292814).length < 2 ^ (prefixWord ++ tailWord_1292814).sum := by decide
  have hdescent : baseEnd_1292814 < baseStart_1292814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292863 : List Nat := [1, 1, 2, 2, 3, 2, 1, 3, 2, 6]
def baseStart_1292863 : Nat := 118140960795 + 1292863 * 2 ^ 59
def prefixEnd_1292863 : Nat := 4983230072969 + 3 ^ 40 * 1292863 * 2
def baseEnd_1292863 : Nat := 221286713137960133755579

theorem tailTrace_1292863 : CollatzResearch.WordTrace tailWord_1292863 prefixEnd_1292863 221286713137960133755579 := by
  unfold tailWord_1292863
  simp only [CollatzResearch.WordTrace]
  refine ⟨47154587515185629266451243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31436391676790419510967495 47154587515185629266451243)
  ·
    refine ⟨70731881272778443899676865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47154587515185629266451243 70731881272778443899676865)
    ·
      refine ⟨53048910954583832924757649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70731881272778443899676865 53048910954583832924757649)
      ·
        refine ⟨39786683215937874693568237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53048910954583832924757649 39786683215937874693568237)
        ·
          refine ⟨14920006205976703010088089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39786683215937874693568237 14920006205976703010088089)
          ·
            refine ⟨11190004654482527257566067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14920006205976703010088089 11190004654482527257566067)
            ·
              refine ⟨16785006981723790886349101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11190004654482527257566067 16785006981723790886349101)
              ·
                refine ⟨6294377618146421582380913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16785006981723790886349101 6294377618146421582380913)
                ·
                  refine ⟨4720783213609816186785685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6294377618146421582380913 4720783213609816186785685)
                  ·
                    refine ⟨221286713137960133755579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4720783213609816186785685 221286713137960133755579)
                    ·
                      rfl

theorem cell23_1292863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 6].length) (baseStart_1292863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292863 prefixEnd_1292863 := by exact prefixLift 1292863
  have htrace : WordTrace (prefixWord ++ tailWord_1292863) baseStart_1292863 baseEnd_1292863 := by
    simpa [prefixWord, tailWord_1292863, baseEnd_1292863] using wordTrace_append hprefix tailTrace_1292863
  have hstable : (prefixWord ++ tailWord_1292863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292863).length < 2 ^ (prefixWord ++ tailWord_1292863).sum := by decide
  have hdescent : baseEnd_1292863 < baseStart_1292863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292868 : List Nat := [2, 3, 5, 1, 1, 1, 2, 2, 1, 2, 3]
def baseStart_1292868 : Nat := 118140960795 + 1292868 * 2 ^ 59
def prefixEnd_1292868 : Nat := 4983230072969 + 3 ^ 40 * 1292868 * 2
def baseEnd_1292868 : Nat := 663862706817152881704215

theorem tailTrace_1292868 : CollatzResearch.WordTrace tailWord_1292868 prefixEnd_1292868 663862706817152881704215 := by
  unfold tailWord_1292868
  simp only [CollatzResearch.WordTrace]
  refine ⟨23577384940083757560191629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31436513253445010080255505 23577384940083757560191629)
  ·
    refine ⟨8841519352531409085071861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23577384940083757560191629 8841519352531409085071861)
    ·
      refine ⟨828892439299819601725487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8841519352531409085071861 828892439299819601725487)
      ·
        refine ⟨1243338658949729402588231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 828892439299819601725487 1243338658949729402588231)
        ·
          refine ⟨1865007988424594103882347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1243338658949729402588231 1865007988424594103882347)
          ·
            refine ⟨2797511982636891155823521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1865007988424594103882347 2797511982636891155823521)
            ·
              refine ⟨2098133986977668366867641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2797511982636891155823521 2098133986977668366867641)
              ·
                refine ⟨1573600490233251275150731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2098133986977668366867641 1573600490233251275150731)
                ·
                  refine ⟨2360400735349876912726097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1573600490233251275150731 2360400735349876912726097)
                  ·
                    refine ⟨1770300551512407684544573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2360400735349876912726097 1770300551512407684544573)
                    ·
                      refine ⟨663862706817152881704215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1770300551512407684544573 663862706817152881704215)
                      ·
                        rfl

theorem cell23_1292868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_1292868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292868 prefixEnd_1292868 := by exact prefixLift 1292868
  have htrace : WordTrace (prefixWord ++ tailWord_1292868) baseStart_1292868 baseEnd_1292868 := by
    simpa [prefixWord, tailWord_1292868, baseEnd_1292868] using wordTrace_append hprefix tailTrace_1292868
  have hstable : (prefixWord ++ tailWord_1292868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292868).length < 2 ^ (prefixWord ++ tailWord_1292868).sum := by decide
  have hdescent : baseEnd_1292868 < baseStart_1292868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292874 : List Nat := [3, 1, 2, 1, 1, 5, 2, 2, 1, 3, 2]
def baseStart_1292874 : Nat := 118140960795 + 1292874 * 2 ^ 59
def prefixEnd_1292874 : Nat := 4983230072969 + 3 ^ 40 * 1292874 * 2
def baseEnd_1292874 : Nat := 663865787701079858229187

theorem tailTrace_1292874 : CollatzResearch.WordTrace tailWord_1292874 prefixEnd_1292874 663865787701079858229187 := by
  unfold tailWord_1292874
  simp only [CollatzResearch.WordTrace]
  refine ⟨11788747179536444536275419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31436659145430518763401117 11788747179536444536275419)
  ·
    refine ⟨17683120769304666804413129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11788747179536444536275419 17683120769304666804413129)
    ·
      refine ⟨13262340576978500103309847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17683120769304666804413129 13262340576978500103309847)
      ·
        refine ⟨19893510865467750154964771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13262340576978500103309847 19893510865467750154964771)
        ·
          refine ⟨29840266298201625232447157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19893510865467750154964771 29840266298201625232447157)
          ·
            refine ⟨2797524965456402365541921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29840266298201625232447157 2797524965456402365541921)
            ·
              refine ⟨2098143724092301774156441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2797524965456402365541921 2098143724092301774156441)
              ·
                refine ⟨1573607793069226330617331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2098143724092301774156441 1573607793069226330617331)
                ·
                  refine ⟨2360411689603839495925997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1573607793069226330617331 2360411689603839495925997)
                  ·
                    refine ⟨885154383601439810972249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2360411689603839495925997 885154383601439810972249)
                    ·
                      refine ⟨663865787701079858229187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 885154383601439810972249 663865787701079858229187)
                      ·
                        rfl

theorem cell23_1292874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 1, 3, 2].length) (baseStart_1292874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292874 prefixEnd_1292874 := by exact prefixLift 1292874
  have htrace : WordTrace (prefixWord ++ tailWord_1292874) baseStart_1292874 baseEnd_1292874 := by
    simpa [prefixWord, tailWord_1292874, baseEnd_1292874] using wordTrace_append hprefix tailTrace_1292874
  have hstable : (prefixWord ++ tailWord_1292874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292874).length < 2 ^ (prefixWord ++ tailWord_1292874).sum := by decide
  have hdescent : baseEnd_1292874 < baseStart_1292874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292887 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 6, 2, 2]
def baseStart_1292887 : Nat := 118140960795 + 1292887 * 2 ^ 59
def prefixEnd_1292887 : Nat := 4983230072969 + 3 ^ 40 * 1292887 * 2
def baseEnd_1292887 : Nat := 663872462949588307366627

theorem tailTrace_1292887 : CollatzResearch.WordTrace tailWord_1292887 prefixEnd_1292887 663872462949588307366627 := by
  unfold tailWord_1292887
  simp only [CollatzResearch.WordTrace]
  refine ⟨47155462867098681365324915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31436975244732454243549943 47155462867098681365324915)
  ·
    refine ⟨70733194300648022047987373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47155462867098681365324915 70733194300648022047987373)
    ·
      refine ⟨26524947862743008267995265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70733194300648022047987373 26524947862743008267995265)
      ·
        refine ⟨19893710897057256200996449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26524947862743008267995265 19893710897057256200996449)
        ·
          refine ⟨14920283172792942150747337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19893710897057256200996449 14920283172792942150747337)
          ·
            refine ⟨11190212379594706613060503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14920283172792942150747337 11190212379594706613060503)
            ·
              refine ⟨16785318569392059919590755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11190212379594706613060503 16785318569392059919590755)
              ·
                refine ⟨25177977854088089879386133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16785318569392059919590755 25177977854088089879386133)
                ·
                  refine ⟨1180217711910379213096225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25177977854088089879386133 1180217711910379213096225)
                  ·
                    refine ⟨885163283932784409822169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1180217711910379213096225 885163283932784409822169)
                    ·
                      refine ⟨663872462949588307366627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 885163283932784409822169 663872462949588307366627)
                      ·
                        rfl

theorem cell23_1292887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6, 2, 2].length) (baseStart_1292887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292887 prefixEnd_1292887 := by exact prefixLift 1292887
  have htrace : WordTrace (prefixWord ++ tailWord_1292887) baseStart_1292887 baseEnd_1292887 := by
    simpa [prefixWord, tailWord_1292887, baseEnd_1292887] using wordTrace_append hprefix tailTrace_1292887
  have hstable : (prefixWord ++ tailWord_1292887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292887).length < 2 ^ (prefixWord ++ tailWord_1292887).sum := by decide
  have hdescent : baseEnd_1292887 < baseStart_1292887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292903 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_1292903 : Nat := 118140960795 + 1292903 * 2 ^ 59
def prefixEnd_1292903 : Nat := 4983230072969 + 3 ^ 40 * 1292903 * 2
def baseEnd_1292903 : Nat := 663880678640060244766553

theorem tailTrace_1292903 : CollatzResearch.WordTrace tailWord_1292903 prefixEnd_1292903 663880678640060244766553 := by
  unfold tailWord_1292903
  simp only [CollatzResearch.WordTrace]
  refine ⟨47156046435040716097907363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31437364290027144065271575 47156046435040716097907363)
  ·
    refine ⟨70734069652561074146861045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47156046435040716097907363 70734069652561074146861045)
    ·
      refine ⟨6631319029927600701268223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70734069652561074146861045 6631319029927600701268223)
      ·
        refine ⟨9946978544891401051902335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6631319029927600701268223 9946978544891401051902335)
        ·
          refine ⟨14920467817337101577853503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9946978544891401051902335 14920467817337101577853503)
          ·
            refine ⟨22380701726005652366780255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14920467817337101577853503 22380701726005652366780255)
            ·
              refine ⟨33571052589008478550170383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22380701726005652366780255 33571052589008478550170383)
              ·
                refine ⟨50356578883512717825255575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33571052589008478550170383 50356578883512717825255575)
                ·
                  refine ⟨75534868325269076737883363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50356578883512717825255575 75534868325269076737883363)
                  ·
                    refine ⟨113302302487903615106825045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75534868325269076737883363 113302302487903615106825045)
                    ·
                      refine ⟨663880678640060244766553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 113302302487903615106825045 663880678640060244766553)
                      ·
                        rfl

theorem cell23_1292903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_1292903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292903 prefixEnd_1292903 := by exact prefixLift 1292903
  have htrace : WordTrace (prefixWord ++ tailWord_1292903) baseStart_1292903 baseEnd_1292903 := by
    simpa [prefixWord, tailWord_1292903, baseEnd_1292903] using wordTrace_append hprefix tailTrace_1292903
  have hstable : (prefixWord ++ tailWord_1292903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292903).length < 2 ^ (prefixWord ++ tailWord_1292903).sum := by decide
  have hdescent : baseEnd_1292903 < baseStart_1292903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292921 : List Nat := [1, 2, 1, 3, 3, 2, 4, 1, 2, 2, 2]
def baseStart_1292921 : Nat := 118140960795 + 1292921 * 2 ^ 59
def prefixEnd_1292921 : Nat := 4983230072969 + 3 ^ 40 * 1292921 * 2
def baseEnd_1292921 : Nat := 663889921291841174341471

theorem tailTrace_1292921 : CollatzResearch.WordTrace tailWord_1292921 prefixEnd_1292921 663889921291841174341471 := by
  unfold tailWord_1292921
  simp only [CollatzResearch.WordTrace]
  refine ⟨47156702948975505172062617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31437801965983670114708411 47156702948975505172062617)
  ·
    refine ⟨35367527211731628879046963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47156702948975505172062617 35367527211731628879046963)
    ·
      refine ⟨53051290817597443318570445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35367527211731628879046963 53051290817597443318570445)
      ·
        refine ⟨19894234056599041244463917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53051290817597443318570445 19894234056599041244463917)
        ·
          refine ⟨7460337771224640466673969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19894234056599041244463917 7460337771224640466673969)
          ·
            refine ⟨5595253328418480350005477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7460337771224640466673969 5595253328418480350005477)
            ·
              refine ⟨1049109999078465065626027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5595253328418480350005477 1049109999078465065626027)
              ·
                refine ⟨1573664998617697598439041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1049109999078465065626027 1573664998617697598439041)
                ·
                  refine ⟨1180248748963273198829281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1573664998617697598439041 1180248748963273198829281)
                  ·
                    refine ⟨885186561722454899121961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1180248748963273198829281 885186561722454899121961)
                    ·
                      refine ⟨663889921291841174341471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 885186561722454899121961 663889921291841174341471)
                      ·
                        rfl

theorem cell23_1292921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 2, 2, 2].length) (baseStart_1292921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292921 prefixEnd_1292921 := by exact prefixLift 1292921
  have htrace : WordTrace (prefixWord ++ tailWord_1292921) baseStart_1292921 baseEnd_1292921 := by
    simpa [prefixWord, tailWord_1292921, baseEnd_1292921] using wordTrace_append hprefix tailTrace_1292921
  have hstable : (prefixWord ++ tailWord_1292921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292921).length < 2 ^ (prefixWord ++ tailWord_1292921).sum := by decide
  have hdescent : baseEnd_1292921 < baseStart_1292921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292923 : List Nat := [1, 1, 1, 1, 1, 4, 2, 4, 1, 7]
def baseStart_1292923 : Nat := 118140960795 + 1292923 * 2 ^ 59
def prefixEnd_1292923 : Nat := 4983230072969 + 3 ^ 40 * 1292923 * 2
def baseEnd_1292923 : Nat := 221296982751050055505487

theorem tailTrace_1292923 : CollatzResearch.WordTrace tailWord_1292923 prefixEnd_1292923 221296982751050055505487 := by
  unfold tailWord_1292923
  simp only [CollatzResearch.WordTrace]
  refine ⟨47156775894968259513635423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31437850596645506342423615 47156775894968259513635423)
  ·
    refine ⟨70735163842452389270453135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47156775894968259513635423 70735163842452389270453135)
    ·
      refine ⟨106102745763678583905679703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70735163842452389270453135 106102745763678583905679703)
      ·
        refine ⟨159154118645517875858519555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106102745763678583905679703 159154118645517875858519555)
        ·
          refine ⟨238731177968276813787779333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159154118645517875858519555 238731177968276813787779333)
          ·
            refine ⟨44762095869051902585208625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 238731177968276813787779333 44762095869051902585208625)
            ·
              refine ⟨33571571901788926938906469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44762095869051902585208625 33571571901788926938906469)
              ·
                refine ⟨6294669731585423801044963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33571571901788926938906469 6294669731585423801044963)
                ·
                  refine ⟨9442004597378135701567445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6294669731585423801044963 9442004597378135701567445)
                  ·
                    refine ⟨221296982751050055505487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9442004597378135701567445 221296982751050055505487)
                    ·
                      rfl

theorem cell23_1292923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 7].length) (baseStart_1292923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292923 prefixEnd_1292923 := by exact prefixLift 1292923
  have htrace : WordTrace (prefixWord ++ tailWord_1292923) baseStart_1292923 baseEnd_1292923 := by
    simpa [prefixWord, tailWord_1292923, baseEnd_1292923] using wordTrace_append hprefix tailTrace_1292923
  have hstable : (prefixWord ++ tailWord_1292923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292923).length < 2 ^ (prefixWord ++ tailWord_1292923).sum := by decide
  have hdescent : baseEnd_1292923 < baseStart_1292923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292961 : List Nat := [1, 2, 3, 3, 3, 2, 2, 2, 5]
def baseStart_1292961 : Nat := 118140960795 + 1292961 * 2 ^ 59
def prefixEnd_1292961 : Nat := 4983230072969 + 3 ^ 40 * 1292961 * 2
def baseEnd_1292961 : Nat := 73767828946446779760143

theorem tailTrace_1292961 : CollatzResearch.WordTrace tailWord_1292961 prefixEnd_1292961 73767828946446779760143 := by
  unfold tailWord_1292961
  simp only [CollatzResearch.WordTrace]
  refine ⟨47158161868830592003518737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31438774579220394669012491 47158161868830592003518737)
  ·
    refine ⟨35368621401622944002639053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47158161868830592003518737 35368621401622944002639053)
    ·
      refine ⟨13263233025608604000989645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35368621401622944002639053 13263233025608604000989645)
      ·
        refine ⟨4973712384603226500371117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13263233025608604000989645 4973712384603226500371117)
        ·
          refine ⟨1865142144226209937639169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4973712384603226500371117 1865142144226209937639169)
          ·
            refine ⟨1398856608169657453229377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1865142144226209937639169 1398856608169657453229377)
            ·
              refine ⟨1049142456127243089922033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1398856608169657453229377 1049142456127243089922033)
              ·
                refine ⟨786856842095432317441525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1049142456127243089922033 786856842095432317441525)
                ·
                  refine ⟨73767828946446779760143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 786856842095432317441525 73767828946446779760143)
                  ·
                    rfl

theorem cell23_1292961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2, 5].length) (baseStart_1292961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1292961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1292961 prefixEnd_1292961 := by exact prefixLift 1292961
  have htrace : WordTrace (prefixWord ++ tailWord_1292961) baseStart_1292961 baseEnd_1292961 := by
    simpa [prefixWord, tailWord_1292961, baseEnd_1292961] using wordTrace_append hprefix tailTrace_1292961
  have hstable : (prefixWord ++ tailWord_1292961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292961).length < 2 ^ (prefixWord ++ tailWord_1292961).sum := by decide
  have hdescent : baseEnd_1292961 < baseStart_1292961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293077 : List Nat := [1, 3, 2, 1, 2, 2, 1, 3, 4, 4]
def baseStart_1293077 : Nat := 118140960795 + 1293077 * 2 ^ 59
def prefixEnd_1293077 : Nat := 4983230072969 + 3 ^ 40 * 1293077 * 2
def baseEnd_1293077 : Nat := 221323341424647521330251

theorem tailTrace_1293077 : CollatzResearch.WordTrace tailWord_1293077 prefixEnd_1293077 221323341424647521330251 := by
  unfold tailWord_1293077
  simp only [CollatzResearch.WordTrace]
  refine ⟨47162392736410343814741485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31441595157606895876494323 47162392736410343814741485)
  ·
    refine ⟨17685897276153878930528057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47162392736410343814741485 17685897276153878930528057)
    ·
      refine ⟨13264422957115409197896043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17685897276153878930528057 13264422957115409197896043)
      ·
        refine ⟨19896634435673113796844065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13264422957115409197896043 19896634435673113796844065)
        ·
          refine ⟨14922475826754835347633049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19896634435673113796844065 14922475826754835347633049)
          ·
            refine ⟨11191856870066126510724787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14922475826754835347633049 11191856870066126510724787)
            ·
              refine ⟨16787785305099189766087181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11191856870066126510724787 16787785305099189766087181)
              ·
                refine ⟨6295419489412196162282693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16787785305099189766087181 6295419489412196162282693)
                ·
                  refine ⟨1180391154264786780428005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6295419489412196162282693 1180391154264786780428005)
                  ·
                    refine ⟨221323341424647521330251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1180391154264786780428005 221323341424647521330251)
                    ·
                      rfl

theorem cell23_1293077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_1293077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293077 prefixEnd_1293077 := by exact prefixLift 1293077
  have htrace : WordTrace (prefixWord ++ tailWord_1293077) baseStart_1293077 baseEnd_1293077 := by
    simpa [prefixWord, tailWord_1293077, baseEnd_1293077] using wordTrace_append hprefix tailTrace_1293077
  have hstable : (prefixWord ++ tailWord_1293077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293077).length < 2 ^ (prefixWord ++ tailWord_1293077).sum := by decide
  have hdescent : baseEnd_1293077 < baseStart_1293077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293087 : List Nat := [1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 5]
def baseStart_1293087 : Nat := 118140960795 + 1293087 * 2 ^ 59
def prefixEnd_1293087 : Nat := 4983230072969 + 3 ^ 40 * 1293087 * 2
def baseEnd_1293087 : Nat := 663975159080487524865707

theorem tailTrace_1293087 : CollatzResearch.WordTrace tailWord_1293087 prefixEnd_1293087 663975159080487524865707 := by
  unfold tailWord_1293087
  simp only [CollatzResearch.WordTrace]
  refine ⟨47162757466374115522605515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31441838310916077015070343 47162757466374115522605515)
  ·
    refine ⟨70744136199561173283908273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47162757466374115522605515 70744136199561173283908273)
    ·
      refine ⟨53058102149670879962931205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70744136199561173283908273 53058102149670879962931205)
      ·
        refine ⟨9948394153063289993049601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53058102149670879962931205 9948394153063289993049601)
        ·
          refine ⟨7461295614797467494787201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9948394153063289993049601 7461295614797467494787201)
          ·
            refine ⟨5595971711098100621090401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7461295614797467494787201 5595971711098100621090401)
            ·
              refine ⟨4196978783323575465817801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5595971711098100621090401 4196978783323575465817801)
              ·
                refine ⟨3147734087492681599363351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4196978783323575465817801 3147734087492681599363351)
                ·
                  refine ⟨4721601131239022399045027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3147734087492681599363351 4721601131239022399045027)
                  ·
                    refine ⟨7082401696858533598567541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4721601131239022399045027 7082401696858533598567541)
                    ·
                      refine ⟨663975159080487524865707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7082401696858533598567541 663975159080487524865707)
                      ·
                        rfl

theorem cell23_1293087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_1293087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293087 prefixEnd_1293087 := by exact prefixLift 1293087
  have htrace : WordTrace (prefixWord ++ tailWord_1293087) baseStart_1293087 baseEnd_1293087 := by
    simpa [prefixWord, tailWord_1293087, baseEnd_1293087] using wordTrace_append hprefix tailTrace_1293087
  have hstable : (prefixWord ++ tailWord_1293087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293087).length < 2 ^ (prefixWord ++ tailWord_1293087).sum := by decide
  have hdescent : baseEnd_1293087 < baseStart_1293087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293098 : List Nat := [3, 1, 4, 3, 1, 2, 1, 2, 1, 5]
def baseStart_1293098 : Nat := 118140960795 + 1293098 * 2 ^ 59
def prefixEnd_1293098 : Nat := 4983230072969 + 3 ^ 40 * 1293098 * 2
def baseEnd_1293098 : Nat := 221326935789228993942719

theorem tailTrace_1293098 : CollatzResearch.WordTrace tailWord_1293098 prefixEnd_1293098 221326935789228993942719 := by
  unfold tailWord_1293098
  simp only [CollatzResearch.WordTrace]
  refine ⟨11790789667333566100313987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31442105779556176267503965 11790789667333566100313987)
  ·
    refine ⟨17686184501000349150470981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11790789667333566100313987 17686184501000349150470981)
    ·
      refine ⟨3316159593937565465713309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17686184501000349150470981 3316159593937565465713309)
      ·
        refine ⟨1243559847726587049642491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3316159593937565465713309 1243559847726587049642491)
        ·
          refine ⟨1865339771589880574463737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1243559847726587049642491 1865339771589880574463737)
          ·
            refine ⟨1399004828692410430847803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1865339771589880574463737 1399004828692410430847803)
            ·
              refine ⟨2098507243038615646271705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1399004828692410430847803 2098507243038615646271705)
              ·
                refine ⟨1573880432278961734703779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2098507243038615646271705 1573880432278961734703779)
                ·
                  refine ⟨2360820648418442602055669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1573880432278961734703779 2360820648418442602055669)
                  ·
                    refine ⟨221326935789228993942719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2360820648418442602055669 221326935789228993942719)
                    ·
                      rfl

theorem cell23_1293098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_1293098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293098 prefixEnd_1293098 := by exact prefixLift 1293098
  have htrace : WordTrace (prefixWord ++ tailWord_1293098) baseStart_1293098 baseEnd_1293098 := by
    simpa [prefixWord, tailWord_1293098, baseEnd_1293098] using wordTrace_append hprefix tailTrace_1293098
  have hstable : (prefixWord ++ tailWord_1293098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293098).length < 2 ^ (prefixWord ++ tailWord_1293098).sum := by decide
  have hdescent : baseEnd_1293098 < baseStart_1293098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293114 : List Nat := [3, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4]
def baseStart_1293114 : Nat := 118140960795 + 1293114 * 2 ^ 59
def prefixEnd_1293114 : Nat := 4983230072969 + 3 ^ 40 * 1293114 * 2
def baseEnd_1293114 : Nat := 663989023058158919228083

theorem tailTrace_1293114 : CollatzResearch.WordTrace tailWord_1293114 prefixEnd_1293114 663989023058158919228083 := by
  unfold tailWord_1293114
  simp only [CollatzResearch.WordTrace]
  refine ⟨11790935559319074783459599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31442494824850866089225597 11790935559319074783459599)
  ·
    refine ⟨17686403338978612175189399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11790935559319074783459599 17686403338978612175189399)
    ·
      refine ⟨26529605008467918262784099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17686403338978612175189399 26529605008467918262784099)
      ·
        refine ⟨39794407512701877394176149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26529605008467918262784099 39794407512701877394176149)
        ·
          refine ⟨1865362852157900502852007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39794407512701877394176149 1865362852157900502852007)
          ·
            refine ⟨2798044278236850754278011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1865362852157900502852007 2798044278236850754278011)
            ·
              refine ⟨4197066417355276131417017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2798044278236850754278011 4197066417355276131417017)
              ·
                refine ⟨3147799813016457098562763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4197066417355276131417017 3147799813016457098562763)
                ·
                  refine ⟨4721699719524685647844145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3147799813016457098562763 4721699719524685647844145)
                  ·
                    refine ⟨3541274789643514235883109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4721699719524685647844145 3541274789643514235883109)
                    ·
                      refine ⟨663989023058158919228083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3541274789643514235883109 663989023058158919228083)
                      ·
                        rfl

theorem cell23_1293114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4].length) (baseStart_1293114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293114 prefixEnd_1293114 := by exact prefixLift 1293114
  have htrace : WordTrace (prefixWord ++ tailWord_1293114) baseStart_1293114 baseEnd_1293114 := by
    simpa [prefixWord, tailWord_1293114, baseEnd_1293114] using wordTrace_append hprefix tailTrace_1293114
  have hstable : (prefixWord ++ tailWord_1293114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293114).length < 2 ^ (prefixWord ++ tailWord_1293114).sum := by decide
  have hdescent : baseEnd_1293114 < baseStart_1293114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293118 : List Nat := [4, 2, 1, 2, 3, 1, 3, 1, 1, 1, 4]
def baseStart_1293118 : Nat := 118140960795 + 1293118 * 2 ^ 59
def prefixEnd_1293118 : Nat := 4983230072969 + 3 ^ 40 * 1293118 * 2
def baseEnd_1293118 : Nat := 663991076980776903578065

theorem tailTrace_1293118 : CollatzResearch.WordTrace tailWord_1293118 prefixEnd_1293118 663991076980776903578065 := by
  unfold tailWord_1293118
  simp only [CollatzResearch.WordTrace]
  refine ⟨5895486016157725977123001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31442592086174538544656005 5895486016157725977123001)
  ·
    refine ⟨4421614512118294482842251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5895486016157725977123001 4421614512118294482842251)
    ·
      refine ⟨6632421768177441724263377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4421614512118294482842251 6632421768177441724263377)
      ·
        refine ⟨4974316326133081293197533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6632421768177441724263377 4974316326133081293197533)
        ·
          refine ⟨1865368622299905484949075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4974316326133081293197533 1865368622299905484949075)
          ·
            refine ⟨2798052933449858227423613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1865368622299905484949075 2798052933449858227423613)
            ·
              refine ⟨1049269850043696835283855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2798052933449858227423613 1049269850043696835283855)
              ·
                refine ⟨1573904775065545252925783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1049269850043696835283855 1573904775065545252925783)
                ·
                  refine ⟨2360857162598317879388675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1573904775065545252925783 2360857162598317879388675)
                  ·
                    refine ⟨3541285743897476819083013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2360857162598317879388675 3541285743897476819083013)
                    ·
                      refine ⟨663991076980776903578065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3541285743897476819083013 663991076980776903578065)
                      ·
                        rfl

theorem cell23_1293118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_1293118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293118 prefixEnd_1293118 := by exact prefixLift 1293118
  have htrace : WordTrace (prefixWord ++ tailWord_1293118) baseStart_1293118 baseEnd_1293118 := by
    simpa [prefixWord, tailWord_1293118, baseEnd_1293118] using wordTrace_append hprefix tailTrace_1293118
  have hstable : (prefixWord ++ tailWord_1293118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293118).length < 2 ^ (prefixWord ++ tailWord_1293118).sum := by decide
  have hdescent : baseEnd_1293118 < baseStart_1293118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293120 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 4, 7]
def baseStart_1293120 : Nat := 118140960795 + 1293120 * 2 ^ 59
def prefixEnd_1293120 : Nat := 4983230072969 + 3 ^ 40 * 1293120 * 2
def baseEnd_1293120 : Nat := 221330701314028631917685

theorem tailTrace_1293120 : CollatzResearch.WordTrace tailWord_1293120 prefixEnd_1293120 221330701314028631917685 := by
  unfold tailWord_1293120
  simp only [CollatzResearch.WordTrace]
  refine ⟨23581980537627281079278407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31442640716836374772371209 23581980537627281079278407)
  ·
    refine ⟨35372970806440921618917611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23581980537627281079278407 35372970806440921618917611)
    ·
      refine ⟨53059456209661382428376417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35372970806440921618917611 53059456209661382428376417)
      ·
        refine ⟨39794592157246036821282313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53059456209661382428376417 39794592157246036821282313)
        ·
          refine ⟨29845944117934527615961735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39794592157246036821282313 29845944117934527615961735)
          ·
            refine ⟨44768916176901791423942603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29845944117934527615961735 44768916176901791423942603)
            ·
              refine ⟨67153374265352687135913905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44768916176901791423942603 67153374265352687135913905)
              ·
                refine ⟨50365030699014515351935429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67153374265352687135913905 50365030699014515351935429)
                ·
                  refine ⟨9443443256065221628487893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50365030699014515351935429 9443443256065221628487893)
                  ·
                    refine ⟨221330701314028631917685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9443443256065221628487893 221330701314028631917685)
                    ·
                      rfl

theorem cell23_1293120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 4, 7].length) (baseStart_1293120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293120 prefixEnd_1293120 := by exact prefixLift 1293120
  have htrace : WordTrace (prefixWord ++ tailWord_1293120) baseStart_1293120 baseEnd_1293120 := by
    simpa [prefixWord, tailWord_1293120, baseEnd_1293120] using wordTrace_append hprefix tailTrace_1293120
  have hstable : (prefixWord ++ tailWord_1293120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293120).length < 2 ^ (prefixWord ++ tailWord_1293120).sum := by decide
  have hdescent : baseEnd_1293120 < baseStart_1293120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293124 : List Nat := [2, 3, 4, 2, 1, 11]
def baseStart_1293124 : Nat := 118140960795 + 1293124 * 2 ^ 59
def prefixEnd_1293124 : Nat := 4983230072969 + 3 ^ 40 * 1293124 * 2
def baseEnd_1293124 : Nat := 2732486246356806090959

theorem tailTrace_1293124 : CollatzResearch.WordTrace tailWord_1293124 prefixEnd_1293124 2732486246356806090959 := by
  unfold tailWord_1293124
  simp only [CollatzResearch.WordTrace]
  refine ⟨23582053483620035420851213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31442737978160047227801617 23582053483620035420851213)
  ·
    refine ⟨8843270056357513282819205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23582053483620035420851213 8843270056357513282819205)
    ·
      refine ⟨1658113135567033740528601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8843270056357513282819205 1658113135567033740528601)
      ·
        refine ⟨1243584851675275305396451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1658113135567033740528601 1243584851675275305396451)
        ·
          refine ⟨1865377277512912958094677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1243584851675275305396451 1865377277512912958094677)
          ·
            refine ⟨2732486246356806090959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1865377277512912958094677 2732486246356806090959)
            ·
              rfl

theorem cell23_1293124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 11].length) (baseStart_1293124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293124 prefixEnd_1293124 := by exact prefixLift 1293124
  have htrace : WordTrace (prefixWord ++ tailWord_1293124) baseStart_1293124 baseEnd_1293124 := by
    simpa [prefixWord, tailWord_1293124, baseEnd_1293124] using wordTrace_append hprefix tailTrace_1293124
  have hstable : (prefixWord ++ tailWord_1293124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293124).length < 2 ^ (prefixWord ++ tailWord_1293124).sum := by decide
  have hdescent : baseEnd_1293124 < baseStart_1293124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293134 : List Nat := [4, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3]
def baseStart_1293134 : Nat := 118140960795 + 1293134 * 2 ^ 59
def prefixEnd_1293134 : Nat := 4983230072969 + 3 ^ 40 * 1293134 * 2
def baseEnd_1293134 : Nat := 663999292671248840977991

theorem tailTrace_1293134 : CollatzResearch.WordTrace tailWord_1293134 prefixEnd_1293134 663999292671248840977991 := by
  unfold tailWord_1293134
  simp only [CollatzResearch.WordTrace]
  refine ⟨5895558962150480318695807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31442981131469228366377637 5895558962150480318695807)
  ·
    refine ⟨8843338443225720478043711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5895558962150480318695807 8843338443225720478043711)
    ·
      refine ⟨13265007664838580717065567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8843338443225720478043711 13265007664838580717065567)
      ·
        refine ⟨19897511497257871075598351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13265007664838580717065567 19897511497257871075598351)
        ·
          refine ⟨29846267245886806613397527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19897511497257871075598351 29846267245886806613397527)
          ·
            refine ⟨44769400868830209920096291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29846267245886806613397527 44769400868830209920096291)
            ·
              refine ⟨67154101303245314880144437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44769400868830209920096291 67154101303245314880144437)
              ·
                refine ⟨6295696997179248270013541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67154101303245314880144437 6295696997179248270013541)
                ·
                  refine ⟨1180443186971109050627539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6295696997179248270013541 1180443186971109050627539)
                  ·
                    refine ⟨1770664780456663575941309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1180443186971109050627539 1770664780456663575941309)
                    ·
                      refine ⟨663999292671248840977991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1770664780456663575941309 663999292671248840977991)
                      ·
                        rfl

theorem cell23_1293134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_1293134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293134 prefixEnd_1293134 := by exact prefixLift 1293134
  have htrace : WordTrace (prefixWord ++ tailWord_1293134) baseStart_1293134 baseEnd_1293134 := by
    simpa [prefixWord, tailWord_1293134, baseEnd_1293134] using wordTrace_append hprefix tailTrace_1293134
  have hstable : (prefixWord ++ tailWord_1293134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293134).length < 2 ^ (prefixWord ++ tailWord_1293134).sum := by decide
  have hdescent : baseEnd_1293134 < baseStart_1293134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293187 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 4]
def baseStart_1293187 : Nat := 118140960795 + 1293187 * 2 ^ 59
def prefixEnd_1293187 : Nat := 4983230072969 + 3 ^ 40 * 1293187 * 2
def baseEnd_1293187 : Nat := 664026507145937133615247

theorem tailTrace_1293187 : CollatzResearch.WordTrace tailWord_1293187 prefixEnd_1293187 664026507145937133615247 := by
  unfold tailWord_1293187
  simp only [CollatzResearch.WordTrace]
  refine ⟨47166404766011832601245815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31444269844007888400830543 47166404766011832601245815)
  ·
    refine ⟨70749607149017748901868723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47166404766011832601245815 70749607149017748901868723)
    ·
      refine ⟨106124410723526623352803085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70749607149017748901868723 106124410723526623352803085)
      ·
        refine ⟨39796654021322483757301157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106124410723526623352803085 39796654021322483757301157)
        ·
          refine ⟨7461872628997965704493967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39796654021322483757301157 7461872628997965704493967)
          ·
            refine ⟨11192808943496948556740951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7461872628997965704493967 11192808943496948556740951)
            ·
              refine ⟨16789213415245422835111427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11192808943496948556740951 16789213415245422835111427)
              ·
                refine ⟨25183820122868134252667141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16789213415245422835111427 25183820122868134252667141)
                ·
                  refine ⟨4721966273037775172375089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25183820122868134252667141 4721966273037775172375089)
                  ·
                    refine ⟨3541474704778331379281317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4721966273037775172375089 3541474704778331379281317)
                    ·
                      refine ⟨664026507145937133615247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3541474704778331379281317 664026507145937133615247)
                      ·
                        rfl

theorem cell23_1293187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_1293187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293187 prefixEnd_1293187 := by exact prefixLift 1293187
  have htrace : WordTrace (prefixWord ++ tailWord_1293187) baseStart_1293187 baseEnd_1293187 := by
    simpa [prefixWord, tailWord_1293187, baseEnd_1293187] using wordTrace_append hprefix tailTrace_1293187
  have hstable : (prefixWord ++ tailWord_1293187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293187).length < 2 ^ (prefixWord ++ tailWord_1293187).sum := by decide
  have hdescent : baseEnd_1293187 < baseStart_1293187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293204 : List Nat := [2, 4, 2, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_1293204 : Nat := 118140960795 + 1293204 * 2 ^ 59
def prefixEnd_1293204 : Nat := 4983230072969 + 3 ^ 40 * 1293204 * 2
def baseEnd_1293204 : Nat := 664035236317063567102669

theorem tailTrace_1293204 : CollatzResearch.WordTrace tailWord_1293204 prefixEnd_1293204 664035236317063567102669 := by
  unfold tailWord_1293204
  simp only [CollatzResearch.WordTrace]
  refine ⟨23583512403475122252307333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31444683204633496336409777 23583512403475122252307333)
  ·
    refine ⟨4421908575651585422307625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23583512403475122252307333 4421908575651585422307625)
    ·
      refine ⟨3316431431738689066730719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4421908575651585422307625 3316431431738689066730719)
      ·
        refine ⟨4974647147608033600096079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3316431431738689066730719 4974647147608033600096079)
        ·
          refine ⟨7461970721412050400144119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4974647147608033600096079 7461970721412050400144119)
          ·
            refine ⟨11192956082118075600216179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7461970721412050400144119 11192956082118075600216179)
            ·
              refine ⟨16789434123177113400324269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11192956082118075600216179 16789434123177113400324269)
              ·
                refine ⟨6296037796191417525121601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16789434123177113400324269 6296037796191417525121601)
                ·
                  refine ⟨4722028347143563143841201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6296037796191417525121601 4722028347143563143841201)
                  ·
                    refine ⟨3541521260357672357880901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4722028347143563143841201 3541521260357672357880901)
                    ·
                      refine ⟨664035236317063567102669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3541521260357672357880901 664035236317063567102669)
                      ·
                        rfl

theorem cell23_1293204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_1293204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293204 prefixEnd_1293204 := by exact prefixLift 1293204
  have htrace : WordTrace (prefixWord ++ tailWord_1293204) baseStart_1293204 baseEnd_1293204 := by
    simpa [prefixWord, tailWord_1293204, baseEnd_1293204] using wordTrace_append hprefix tailTrace_1293204
  have hstable : (prefixWord ++ tailWord_1293204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293204).length < 2 ^ (prefixWord ++ tailWord_1293204).sum := by decide
  have hdescent : baseEnd_1293204 < baseStart_1293204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293234 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2]
def baseStart_1293234 : Nat := 118140960795 + 1293234 * 2 ^ 59
def prefixEnd_1293234 : Nat := 4983230072969 + 3 ^ 40 * 1293234 * 2
def baseEnd_1293234 : Nat := 664050640736698449727531

theorem tailTrace_1293234 : CollatzResearch.WordTrace tailWord_1293234 prefixEnd_1293234 664050640736698449727531 := by
  unfold tailWord_1293234
  simp only [CollatzResearch.WordTrace]
  refine ⟨11792029749210389907051689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31445412664561039752137837 11792029749210389907051689)
  ·
    refine ⟨8844022311907792430288767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11792029749210389907051689 8844022311907792430288767)
    ·
      refine ⟨13266033467861688645433151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8844022311907792430288767 13266033467861688645433151)
      ·
        refine ⟨19899050201792532968149727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13266033467861688645433151 19899050201792532968149727)
        ·
          refine ⟨29848575302688799452224591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19899050201792532968149727 29848575302688799452224591)
          ·
            refine ⟨44772862954033199178336887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29848575302688799452224591 44772862954033199178336887)
            ·
              refine ⟨67159294431049798767505331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44772862954033199178336887 67159294431049798767505331)
              ·
                refine ⟨100738941646574698151257997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67159294431049798767505331 100738941646574698151257997)
                ·
                  refine ⟨37777103117465511806721749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100738941646574698151257997 37777103117465511806721749)
                  ·
                    refine ⟨885400854315597932970041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37777103117465511806721749 885400854315597932970041)
                    ·
                      refine ⟨664050640736698449727531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 885400854315597932970041 664050640736698449727531)
                      ·
                        rfl

theorem cell23_1293234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2].length) (baseStart_1293234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293234 prefixEnd_1293234 := by exact prefixLift 1293234
  have htrace : WordTrace (prefixWord ++ tailWord_1293234) baseStart_1293234 baseEnd_1293234 := by
    simpa [prefixWord, tailWord_1293234, baseEnd_1293234] using wordTrace_append hprefix tailTrace_1293234
  have hstable : (prefixWord ++ tailWord_1293234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293234).length < 2 ^ (prefixWord ++ tailWord_1293234).sum := by decide
  have hdescent : baseEnd_1293234 < baseStart_1293234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293247 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 4]
def baseStart_1293247 : Nat := 118140960795 + 1293247 * 2 ^ 59
def prefixEnd_1293247 : Nat := 4983230072969 + 3 ^ 40 * 1293247 * 2
def baseEnd_1293247 : Nat := 664057315985206898864971

theorem tailTrace_1293247 : CollatzResearch.WordTrace tailWord_1293247 prefixEnd_1293247 664057315985206898864971 := by
  unfold tailWord_1293247
  simp only [CollatzResearch.WordTrace]
  refine ⟨47168593145794462848429995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31445728763862975232286663 47168593145794462848429995)
  ·
    refine ⟨70752889718691694272644993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47168593145794462848429995 70752889718691694272644993)
    ·
      refine ⟨53064667289018770704483745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70752889718691694272644993 53064667289018770704483745)
      ·
        refine ⟨39798500466764078028362809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53064667289018770704483745 39798500466764078028362809)
        ·
          refine ⟨29848875350073058521272107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39798500466764078028362809 29848875350073058521272107)
          ·
            refine ⟨44773313025109587781908161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29848875350073058521272107 44773313025109587781908161)
            ·
              refine ⟨33579984768832190836431121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44773313025109587781908161 33579984768832190836431121)
              ·
                refine ⟨25184988576624143127323341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33579984768832190836431121 25184988576624143127323341)
                ·
                  refine ⟨9444370716234053672746253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25184988576624143127323341 9444370716234053672746253)
                  ·
                    refine ⟨3541639018587770127279845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9444370716234053672746253 3541639018587770127279845)
                    ·
                      refine ⟨664057315985206898864971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3541639018587770127279845 664057315985206898864971)
                      ·
                        rfl

theorem cell23_1293247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_1293247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293247 prefixEnd_1293247 := by exact prefixLift 1293247
  have htrace : WordTrace (prefixWord ++ tailWord_1293247) baseStart_1293247 baseEnd_1293247 := by
    simpa [prefixWord, tailWord_1293247, baseEnd_1293247] using wordTrace_append hprefix tailTrace_1293247
  have hstable : (prefixWord ++ tailWord_1293247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293247).length < 2 ^ (prefixWord ++ tailWord_1293247).sum := by decide
  have hdescent : baseEnd_1293247 < baseStart_1293247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293264 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 1, 6, 2]
def baseStart_1293264 : Nat := 118140960795 + 1293264 * 2 ^ 59
def prefixEnd_1293264 : Nat := 4983230072969 + 3 ^ 40 * 1293264 * 2
def baseEnd_1293264 : Nat := 664066045156333332352393

theorem tailTrace_1293264 : CollatzResearch.WordTrace tailWord_1293264 prefixEnd_1293264 664066045156333332352393 := by
  unfold tailWord_1293264
  simp only [CollatzResearch.WordTrace]
  refine ⟨23584606593366437375899423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31446142124488583167865897 23584606593366437375899423)
  ·
    refine ⟨35376909890049656063849135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23584606593366437375899423 35376909890049656063849135)
    ·
      refine ⟨53065364835074484095773703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35376909890049656063849135 53065364835074484095773703)
      ·
        refine ⟨79598047252611726143660555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53065364835074484095773703 79598047252611726143660555)
        ·
          refine ⟨119397070878917589215490833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79598047252611726143660555 119397070878917589215490833)
          ·
            refine ⟨89547803159188191911618125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119397070878917589215490833 89547803159188191911618125)
            ·
              refine ⟨33580426184695571966856797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89547803159188191911618125 33580426184695571966856797)
              ·
                refine ⟨12592659819260839487571299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33580426184695571966856797 12592659819260839487571299)
                ·
                  refine ⟨18888989728891259231356949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12592659819260839487571299 18888989728891259231356949)
                  ·
                    refine ⟨885421393541777776469857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18888989728891259231356949 885421393541777776469857)
                    ·
                      refine ⟨664066045156333332352393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 885421393541777776469857 664066045156333332352393)
                      ·
                        rfl

theorem cell23_1293264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 1, 6, 2].length) (baseStart_1293264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293264 prefixEnd_1293264 := by exact prefixLift 1293264
  have htrace : WordTrace (prefixWord ++ tailWord_1293264) baseStart_1293264 baseEnd_1293264 := by
    simpa [prefixWord, tailWord_1293264, baseEnd_1293264] using wordTrace_append hprefix tailTrace_1293264
  have hstable : (prefixWord ++ tailWord_1293264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293264).length < 2 ^ (prefixWord ++ tailWord_1293264).sum := by decide
  have hdescent : baseEnd_1293264 < baseStart_1293264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293307 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 6]
def baseStart_1293307 : Nat := 118140960795 + 1293307 * 2 ^ 59
def prefixEnd_1293307 : Nat := 4983230072969 + 3 ^ 40 * 1293307 * 2
def baseEnd_1293307 : Nat := 664088124824476664114695

theorem tailTrace_1293307 : CollatzResearch.WordTrace tailWord_1293307 prefixEnd_1293307 664088124824476664114695 := by
  unfold tailWord_1293307
  simp only [CollatzResearch.WordTrace]
  refine ⟨47170781525577093095614175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31447187683718062063742783 47170781525577093095614175)
  ·
    refine ⟨70756172288365639643421263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47170781525577093095614175 70756172288365639643421263)
    ·
      refine ⟨106134258432548459465131895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70756172288365639643421263 106134258432548459465131895)
      ·
        refine ⟨159201387648822689197697843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106134258432548459465131895 159201387648822689197697843)
        ·
          refine ⟨238802081473234033796546765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159201387648822689197697843 238802081473234033796546765)
          ·
            refine ⟨89550780552462762673705037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 238802081473234033796546765 89550780552462762673705037)
            ·
              refine ⟨33581542707173536002639389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89550780552462762673705037 33581542707173536002639389)
              ·
                refine ⟨12593078515190076000989771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33581542707173536002639389 12593078515190076000989771)
                ·
                  refine ⟨18889617772785114001484657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12593078515190076000989771 18889617772785114001484657)
                  ·
                    refine ⟨14167213329588835501113493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18889617772785114001484657 14167213329588835501113493)
                    ·
                      refine ⟨664088124824476664114695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14167213329588835501113493 664088124824476664114695)
                      ·
                        rfl

theorem cell23_1293307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 6].length) (baseStart_1293307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293307 prefixEnd_1293307 := by exact prefixLift 1293307
  have htrace : WordTrace (prefixWord ++ tailWord_1293307) baseStart_1293307 baseEnd_1293307 := by
    simpa [prefixWord, tailWord_1293307, baseEnd_1293307] using wordTrace_append hprefix tailTrace_1293307
  have hstable : (prefixWord ++ tailWord_1293307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293307).length < 2 ^ (prefixWord ++ tailWord_1293307).sum := by decide
  have hdescent : baseEnd_1293307 < baseStart_1293307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293308 : List Nat := [2, 2, 2, 1, 2, 4, 1, 4, 1, 4]
def baseStart_1293308 : Nat := 118140960795 + 1293308 * 2 ^ 59
def prefixEnd_1293308 : Nat := 4983230072969 + 3 ^ 40 * 1293308 * 2
def baseEnd_1293308 : Nat := 221362879435043720067397

theorem tailTrace_1293308 : CollatzResearch.WordTrace tailWord_1293308 prefixEnd_1293308 221362879435043720067397 := by
  unfold tailWord_1293308
  simp only [CollatzResearch.WordTrace]
  refine ⟨23585408999286735133200289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31447211999048980177600385 23585408999286735133200289)
  ·
    refine ⟨17689056749465051349900217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23585408999286735133200289 17689056749465051349900217)
    ·
      refine ⟨13266792562098788512425163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17689056749465051349900217 13266792562098788512425163)
      ·
        refine ⟨19900188843148182768637745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13266792562098788512425163 19900188843148182768637745)
        ·
          refine ⟨14925141632361137076478309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19900188843148182768637745 14925141632361137076478309)
          ·
            refine ⟨2798464056067713201839683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14925141632361137076478309 2798464056067713201839683)
            ·
              refine ⟨4197696084101569802759525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2798464056067713201839683 4197696084101569802759525)
              ·
                refine ⟨787068015769044338017411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4197696084101569802759525 787068015769044338017411)
                ·
                  refine ⟨1180602023653566507026117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 787068015769044338017411 1180602023653566507026117)
                  ·
                    refine ⟨221362879435043720067397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1180602023653566507026117 221362879435043720067397)
                    ·
                      rfl

theorem cell23_1293308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_1293308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293308 prefixEnd_1293308 := by exact prefixLift 1293308
  have htrace : WordTrace (prefixWord ++ tailWord_1293308) baseStart_1293308 baseEnd_1293308 := by
    simpa [prefixWord, tailWord_1293308, baseEnd_1293308] using wordTrace_append hprefix tailTrace_1293308
  have hstable : (prefixWord ++ tailWord_1293308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293308).length < 2 ^ (prefixWord ++ tailWord_1293308).sum := by decide
  have hdescent : baseEnd_1293308 < baseStart_1293308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293358 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 4, 3, 2]
def baseStart_1293358 : Nat := 118140960795 + 1293358 * 2 ^ 59
def prefixEnd_1293358 : Nat := 4983230072969 + 3 ^ 40 * 1293358 * 2
def baseEnd_1293358 : Nat := 664114312337855964576961

theorem tailTrace_1293358 : CollatzResearch.WordTrace tailWord_1293358 prefixEnd_1293358 664114312337855964576961 := by
  unfold tailWord_1293358
  simp only [CollatzResearch.WordTrace]
  refine ⟨5896580206049041100715091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31448427765594885870480485 5896580206049041100715091)
  ·
    refine ⟨8844870309073561651072637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5896580206049041100715091 8844870309073561651072637)
    ·
      refine ⟨3316826365902585619152239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8844870309073561651072637 3316826365902585619152239)
      ·
        refine ⟨4975239548853878428728359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3316826365902585619152239 4975239548853878428728359)
        ·
          refine ⟨7462859323280817643092539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4975239548853878428728359 7462859323280817643092539)
          ·
            refine ⟨11194288984921226464638809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7462859323280817643092539 11194288984921226464638809)
            ·
              refine ⟨8395716738690919848479107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11194288984921226464638809 8395716738690919848479107)
              ·
                refine ⟨12593575108036379772718661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8395716738690919848479107 12593575108036379772718661)
                ·
                  refine ⟨2361295332756821207384749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12593575108036379772718661 2361295332756821207384749)
                  ·
                    refine ⟨885485749783807952769281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2361295332756821207384749 885485749783807952769281)
                    ·
                      refine ⟨664114312337855964576961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 885485749783807952769281 664114312337855964576961)
                      ·
                        rfl

theorem cell23_1293358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_1293358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293358 prefixEnd_1293358 := by exact prefixLift 1293358
  have htrace : WordTrace (prefixWord ++ tailWord_1293358) baseStart_1293358 baseEnd_1293358 := by
    simpa [prefixWord, tailWord_1293358, baseEnd_1293358] using wordTrace_append hprefix tailTrace_1293358
  have hstable : (prefixWord ++ tailWord_1293358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293358).length < 2 ^ (prefixWord ++ tailWord_1293358).sum := by decide
  have hdescent : baseEnd_1293358 < baseStart_1293358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293381 : List Nat := [1, 3, 1, 1, 1, 3, 2, 5, 2, 4]
def baseStart_1293381 : Nat := 118140960795 + 1293381 * 2 ^ 59
def prefixEnd_1293381 : Nat := 4983230072969 + 3 ^ 40 * 1293381 * 2
def baseEnd_1293381 : Nat := 221375374130969791529785

theorem tailTrace_1293381 : CollatzResearch.WordTrace tailWord_1293381 prefixEnd_1293381 221375374130969791529785 := by
  unfold tailWord_1293381
  simp only [CollatzResearch.WordTrace]
  refine ⟨47173480527309003733807997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31448987018206002489205331 47173480527309003733807997)
  ·
    refine ⟨17690055197740876400177999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47173480527309003733807997 17690055197740876400177999)
    ·
      refine ⟨26535082796611314600266999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17690055197740876400177999 26535082796611314600266999)
      ·
        refine ⟨39802624194916971900400499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26535082796611314600266999 39802624194916971900400499)
        ·
          refine ⟨59703936292375457850600749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39802624194916971900400499 59703936292375457850600749)
          ·
            refine ⟨22388976109640796693975281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59703936292375457850600749 22388976109640796693975281)
            ·
              refine ⟨16791732082230597520481461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22388976109640796693975281 16791732082230597520481461)
              ·
                refine ⟨1574224882709118517545137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16791732082230597520481461 1574224882709118517545137)
                ·
                  refine ⟨1180668662031838888158853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1574224882709118517545137 1180668662031838888158853)
                  ·
                    refine ⟨221375374130969791529785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1180668662031838888158853 221375374130969791529785)
                    ·
                      rfl

theorem cell23_1293381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2, 4].length) (baseStart_1293381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293381 prefixEnd_1293381 := by exact prefixLift 1293381
  have htrace : WordTrace (prefixWord ++ tailWord_1293381) baseStart_1293381 baseEnd_1293381 := by
    simpa [prefixWord, tailWord_1293381, baseEnd_1293381] using wordTrace_append hprefix tailTrace_1293381
  have hstable : (prefixWord ++ tailWord_1293381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293381).length < 2 ^ (prefixWord ++ tailWord_1293381).sum := by decide
  have hdescent : baseEnd_1293381 < baseStart_1293381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293384 : List Nat := [2, 1, 3, 1, 1, 1, 5, 1, 1, 1, 6]
def baseStart_1293384 : Nat := 118140960795 + 1293384 * 2 ^ 59
def prefixEnd_1293384 : Nat := 4983230072969 + 3 ^ 40 * 1293384 * 2
def baseEnd_1293384 : Nat := 664127662834872862851841

theorem tailTrace_1293384 : CollatzResearch.WordTrace tailWord_1293384 prefixEnd_1293384 664127662834872862851841 := by
  unfold tailWord_1293384
  simp only [CollatzResearch.WordTrace]
  refine ⟨23586794973149067623083603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31449059964198756830778137 23586794973149067623083603)
  ·
    refine ⟨35380192459723601434625405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23586794973149067623083603 35380192459723601434625405)
    ·
      refine ⟨13267572172396350537984527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35380192459723601434625405 13267572172396350537984527)
      ·
        refine ⟨19901358258594525806976791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13267572172396350537984527 19901358258594525806976791)
        ·
          refine ⟨29852037387891788710465187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19901358258594525806976791 29852037387891788710465187)
          ·
            refine ⟨44778056081837683065697781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29852037387891788710465187 44778056081837683065697781)
            ·
              refine ⟨4197942757672282787409167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44778056081837683065697781 4197942757672282787409167)
              ·
                refine ⟨6296914136508424181113751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4197942757672282787409167 6296914136508424181113751)
                ·
                  refine ⟨9445371204762636271670627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6296914136508424181113751 9445371204762636271670627)
                  ·
                    refine ⟨14168056807143954407505941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9445371204762636271670627 14168056807143954407505941)
                    ·
                      refine ⟨664127662834872862851841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14168056807143954407505941 664127662834872862851841)
                      ·
                        rfl

theorem cell23_1293384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_1293384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293384 prefixEnd_1293384 := by exact prefixLift 1293384
  have htrace : WordTrace (prefixWord ++ tailWord_1293384) baseStart_1293384 baseEnd_1293384 := by
    simpa [prefixWord, tailWord_1293384, baseEnd_1293384] using wordTrace_append hprefix tailTrace_1293384
  have hstable : (prefixWord ++ tailWord_1293384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293384).length < 2 ^ (prefixWord ++ tailWord_1293384).sum := by decide
  have hdescent : baseEnd_1293384 < baseStart_1293384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293422 : List Nat := [4, 1, 2, 2, 1, 4, 1, 1, 3, 2, 2]
def baseStart_1293422 : Nat := 118140960795 + 1293422 * 2 ^ 59
def prefixEnd_1293422 : Nat := 4983230072969 + 3 ^ 40 * 1293422 * 2
def baseEnd_1293422 : Nat := 664147175099743714176667

theorem tailTrace_1293422 : CollatzResearch.WordTrace tailWord_1293422 prefixEnd_1293422 664147175099743714176667 := by
  unfold tailWord_1293422
  simp only [CollatzResearch.WordTrace]
  refine ⟨5896871990020058467006315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31449983946773645157367013 5896871990020058467006315)
  ·
    refine ⟨8845307985030087700509473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5896871990020058467006315 8845307985030087700509473)
    ·
      refine ⟨6633980988772565775382105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8845307985030087700509473 6633980988772565775382105)
      ·
        refine ⟨4975485741579424331536579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6633980988772565775382105 4975485741579424331536579)
        ·
          refine ⟨7463228612369136497304869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4975485741579424331536579 7463228612369136497304869)
          ·
            refine ⟨1399355364819213093244663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7463228612369136497304869 1399355364819213093244663)
            ·
              refine ⟨2099033047228819639866995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1399355364819213093244663 2099033047228819639866995)
              ·
                refine ⟨3148549570843229459800493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2099033047228819639866995 3148549570843229459800493)
                ·
                  refine ⟨1180706089066211047425185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3148549570843229459800493 1180706089066211047425185)
                  ·
                    refine ⟨885529566799658285568889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1180706089066211047425185 885529566799658285568889)
                    ·
                      refine ⟨664147175099743714176667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 885529566799658285568889 664147175099743714176667)
                      ·
                        rfl

theorem cell23_1293422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_1293422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293422 prefixEnd_1293422 := by exact prefixLift 1293422
  have htrace : WordTrace (prefixWord ++ tailWord_1293422) baseStart_1293422 baseEnd_1293422 := by
    simpa [prefixWord, tailWord_1293422, baseEnd_1293422] using wordTrace_append hprefix tailTrace_1293422
  have hstable : (prefixWord ++ tailWord_1293422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293422).length < 2 ^ (prefixWord ++ tailWord_1293422).sum := by decide
  have hdescent : baseEnd_1293422 < baseStart_1293422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293424 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 2, 7]
def baseStart_1293424 : Nat := 118140960795 + 1293424 * 2 ^ 59
def prefixEnd_1293424 : Nat := 4983230072969 + 3 ^ 40 * 1293424 * 2
def baseEnd_1293424 : Nat := 221382734020350902117219

theorem tailTrace_1293424 : CollatzResearch.WordTrace tailWord_1293424 prefixEnd_1293424 221382734020350902117219 := by
  unfold tailWord_1293424
  simp only [CollatzResearch.WordTrace]
  refine ⟨23587524433076611038811663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31450032577435481385082217 23587524433076611038811663)
  ·
    refine ⟨35381286649614916558217495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23587524433076611038811663 35381286649614916558217495)
    ·
      refine ⟨53071929974422374837326243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35381286649614916558217495 53071929974422374837326243)
      ·
        refine ⟨79607894961633562255989365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53071929974422374837326243 79607894961633562255989365)
        ·
          refine ⟨7463240152653146461499003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79607894961633562255989365 7463240152653146461499003)
          ·
            refine ⟨11194860228979719692248505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7463240152653146461499003 11194860228979719692248505)
            ·
              refine ⟨8396145171734789769186379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11194860228979719692248505 8396145171734789769186379)
              ·
                refine ⟨12594217757602184653779569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8396145171734789769186379 12594217757602184653779569)
                ·
                  refine ⟨9445663318201638490334677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12594217757602184653779569 9445663318201638490334677)
                  ·
                    refine ⟨221382734020350902117219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9445663318201638490334677 221382734020350902117219)
                    ·
                      rfl

theorem cell23_1293424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 2, 7].length) (baseStart_1293424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293424 prefixEnd_1293424 := by exact prefixLift 1293424
  have htrace : WordTrace (prefixWord ++ tailWord_1293424) baseStart_1293424 baseEnd_1293424 := by
    simpa [prefixWord, tailWord_1293424, baseEnd_1293424] using wordTrace_append hprefix tailTrace_1293424
  have hstable : (prefixWord ++ tailWord_1293424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293424).length < 2 ^ (prefixWord ++ tailWord_1293424).sum := by decide
  have hdescent : baseEnd_1293424 < baseStart_1293424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293495 : List Nat := [1, 1, 3, 1, 4, 1, 1, 5, 2, 2, 2]
def baseStart_1293495 : Nat := 118140960795 + 1293495 * 2 ^ 59
def prefixEnd_1293495 : Nat := 4983230072969 + 3 ^ 40 * 1293495 * 2
def baseEnd_1293495 : Nat := 664184659187521928563831

theorem tailTrace_1293495 : CollatzResearch.WordTrace tailWord_1293495 prefixEnd_1293495 664184659187521928563831 := by
  unfold tailWord_1293495
  simp only [CollatzResearch.WordTrace]
  refine ⟨47177638448896001203457939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31451758965930667468971959 47177638448896001203457939)
  ·
    refine ⟨70766457673344001805186909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47177638448896001203457939 70766457673344001805186909)
    ·
      refine ⟨26537421627504000676945091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70766457673344001805186909 26537421627504000676945091)
      ·
        refine ⟨39806132441256001015417637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26537421627504000676945091 39806132441256001015417637)
        ·
          refine ⟨7463649832735500190390807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39806132441256001015417637 7463649832735500190390807)
          ·
            refine ⟨11195474749103250285586211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7463649832735500190390807 11195474749103250285586211)
            ·
              refine ⟨16793212123654875428379317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11195474749103250285586211 16793212123654875428379317)
              ·
                refine ⟨1574363636592644571410561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16793212123654875428379317 1574363636592644571410561)
                ·
                  refine ⟨1180772727444483428557921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1574363636592644571410561 1180772727444483428557921)
                  ·
                    refine ⟨885579545583362571418441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1180772727444483428557921 885579545583362571418441)
                    ·
                      refine ⟨664184659187521928563831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 885579545583362571418441 664184659187521928563831)
                      ·
                        rfl

theorem cell23_1293495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2, 2, 2].length) (baseStart_1293495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293495 prefixEnd_1293495 := by exact prefixLift 1293495
  have htrace : WordTrace (prefixWord ++ tailWord_1293495) baseStart_1293495 baseEnd_1293495 := by
    simpa [prefixWord, tailWord_1293495, baseEnd_1293495] using wordTrace_append hprefix tailTrace_1293495
  have hstable : (prefixWord ++ tailWord_1293495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293495).length < 2 ^ (prefixWord ++ tailWord_1293495).sum := by decide
  have hdescent : baseEnd_1293495 < baseStart_1293495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293591 : List Nat := [1, 1, 3, 4, 1, 1, 1, 3, 8]
def baseStart_1293591 : Nat := 118140960795 + 1293591 * 2 ^ 59
def prefixEnd_1293591 : Nat := 4983230072969 + 3 ^ 40 * 1293591 * 2
def baseEnd_1293591 : Nat := 73803772592261505884821

theorem tailTrace_1293591 : CollatzResearch.WordTrace tailWord_1293591 prefixEnd_1293591 73803772592261505884821 := by
  unfold tailWord_1293591
  simp only [CollatzResearch.WordTrace]
  refine ⟨47181139856548209598952627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31454093237698806399301751 47181139856548209598952627)
  ·
    refine ⟨70771709784822314398428941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47181139856548209598952627 70771709784822314398428941)
    ·
      refine ⟨26539391169308367899410853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70771709784822314398428941 26539391169308367899410853)
      ·
        refine ⟨4976135844245318981139535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26539391169308367899410853 4976135844245318981139535)
        ·
          refine ⟨7464203766367978471709303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4976135844245318981139535 7464203766367978471709303)
          ·
            refine ⟨11196305649551967707563955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7464203766367978471709303 11196305649551967707563955)
            ·
              refine ⟨16794458474327951561345933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11196305649551967707563955 16794458474327951561345933)
              ·
                refine ⟨6297921927872981835504725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16794458474327951561345933 6297921927872981835504725)
                ·
                  refine ⟨73803772592261505884821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6297921927872981835504725 73803772592261505884821)
                  ·
                    rfl

theorem cell23_1293591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 8].length) (baseStart_1293591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293591 prefixEnd_1293591 := by exact prefixLift 1293591
  have htrace : WordTrace (prefixWord ++ tailWord_1293591) baseStart_1293591 baseEnd_1293591 := by
    simpa [prefixWord, tailWord_1293591, baseEnd_1293591] using wordTrace_append hprefix tailTrace_1293591
  have hstable : (prefixWord ++ tailWord_1293591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293591).length < 2 ^ (prefixWord ++ tailWord_1293591).sum := by decide
  have hdescent : baseEnd_1293591 < baseStart_1293591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293651 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 3, 6]
def baseStart_1293651 : Nat := 118140960795 + 1293651 * 2 ^ 59
def prefixEnd_1293651 : Nat := 4983230072969 + 3 ^ 40 * 1293651 * 2
def baseEnd_1293651 : Nat := 221421587389874439404371

theorem tailTrace_1293651 : CollatzResearch.WordTrace tailWord_1293651 prefixEnd_1293651 221421587389874439404371 := by
  unfold tailWord_1293651
  simp only [CollatzResearch.WordTrace]
  refine ⟨47183328236330839846136807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31455552157553893230757871 47183328236330839846136807)
  ·
    refine ⟨70774992354496259769205211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47183328236330839846136807 70774992354496259769205211)
    ·
      refine ⟨106162488531744389653807817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70774992354496259769205211 106162488531744389653807817)
      ·
        refine ⟨79621866398808292240355863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106162488531744389653807817 79621866398808292240355863)
        ·
          refine ⟨119432799598212438360533795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79621866398808292240355863 119432799598212438360533795)
          ·
            refine ⟨179149199397318657540800693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119432799598212438360533795 179149199397318657540800693)
            ·
              refine ⟨16795237443498624144450065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 179149199397318657540800693 16795237443498624144450065)
              ·
                refine ⟨12596428082623968108337549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16795237443498624144450065 12596428082623968108337549)
                ·
                  refine ⟨4723660530983988040626581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12596428082623968108337549 4723660530983988040626581)
                  ·
                    refine ⟨221421587389874439404371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4723660530983988040626581 221421587389874439404371)
                    ·
                      rfl

theorem cell23_1293651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 6].length) (baseStart_1293651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293651 prefixEnd_1293651 := by exact prefixLift 1293651
  have htrace : WordTrace (prefixWord ++ tailWord_1293651) baseStart_1293651 baseEnd_1293651 := by
    simpa [prefixWord, tailWord_1293651, baseEnd_1293651] using wordTrace_append hprefix tailTrace_1293651
  have hstable : (prefixWord ++ tailWord_1293651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293651).length < 2 ^ (prefixWord ++ tailWord_1293651).sum := by decide
  have hdescent : baseEnd_1293651 < baseStart_1293651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293658 : List Nat := [3, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4]
def baseStart_1293658 : Nat := 118140960795 + 1293658 * 2 ^ 59
def prefixEnd_1293658 : Nat := 4983230072969 + 3 ^ 40 * 1293658 * 2
def baseEnd_1293658 : Nat := 664268356534204790825581

theorem tailTrace_1293658 : CollatzResearch.WordTrace tailWord_1293658 prefixEnd_1293658 664268356534204790825581 := by
  unfold tailWord_1293658
  simp only [CollatzResearch.WordTrace]
  refine ⟨11795895886826370010410407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31455722364870320027761085 11795895886826370010410407)
  ·
    refine ⟨17693843830239555015615611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11795895886826370010410407 17693843830239555015615611)
    ·
      refine ⟨26540765745359332523423417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17693843830239555015615611 26540765745359332523423417)
      ·
        refine ⟨19905574309019499392567563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26540765745359332523423417 19905574309019499392567563)
        ·
          refine ⟨29858361463529249088851345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19905574309019499392567563 29858361463529249088851345)
          ·
            refine ⟨22393771097646936816638509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29858361463529249088851345 22393771097646936816638509)
            ·
              refine ⟨8397664161617601306239441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22393771097646936816638509 8397664161617601306239441)
              ·
                refine ⟨6298248121213200979679581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8397664161617601306239441 6298248121213200979679581)
                ·
                  refine ⟨2361843045454950367379843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6298248121213200979679581 2361843045454950367379843)
                  ·
                    refine ⟨3542764568182425551069765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2361843045454950367379843 3542764568182425551069765)
                    ·
                      refine ⟨664268356534204790825581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3542764568182425551069765 664268356534204790825581)
                      ·
                        rfl

theorem cell23_1293658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_1293658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293658 prefixEnd_1293658 := by exact prefixLift 1293658
  have htrace : WordTrace (prefixWord ++ tailWord_1293658) baseStart_1293658 baseEnd_1293658 := by
    simpa [prefixWord, tailWord_1293658, baseEnd_1293658] using wordTrace_append hprefix tailTrace_1293658
  have hstable : (prefixWord ++ tailWord_1293658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293658).length < 2 ^ (prefixWord ++ tailWord_1293658).sum := by decide
  have hdescent : baseEnd_1293658 < baseStart_1293658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293668 : List Nat := [2, 3, 1, 1, 3, 2, 1, 3, 1, 6]
def baseStart_1293668 : Nat := 118140960795 + 1293668 * 2 ^ 59
def prefixEnd_1293668 : Nat := 4983230072969 + 3 ^ 40 * 1293668 * 2
def baseEnd_1293668 : Nat := 221424497113583250566845

theorem tailTrace_1293668 : CollatzResearch.WordTrace tailWord_1293668 prefixEnd_1293668 221424497113583250566845 := by
  unfold tailWord_1293668
  simp only [CollatzResearch.WordTrace]
  refine ⟨23591974138634625874752829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31455965518179501166337105 23591974138634625874752829)
  ·
    refine ⟨8846990301987984703032311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23591974138634625874752829 8846990301987984703032311)
    ·
      refine ⟨13270485452981977054548467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8846990301987984703032311 13270485452981977054548467)
      ·
        refine ⟨19905728179472965581822701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13270485452981977054548467 19905728179472965581822701)
        ·
          refine ⟨7464648067302362093183513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19905728179472965581822701 7464648067302362093183513)
          ·
            refine ⟨5598486050476771569887635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7464648067302362093183513 5598486050476771569887635)
            ·
              refine ⟨8397729075715157354831453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5598486050476771569887635 8397729075715157354831453)
              ·
                refine ⟨3149148403393184008061795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8397729075715157354831453 3149148403393184008061795)
                ·
                  refine ⟨4723722605089776012092693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3149148403393184008061795 4723722605089776012092693)
                  ·
                    refine ⟨221424497113583250566845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4723722605089776012092693 221424497113583250566845)
                    ·
                      rfl

theorem cell23_1293668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_1293668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293668 prefixEnd_1293668 := by exact prefixLift 1293668
  have htrace : WordTrace (prefixWord ++ tailWord_1293668) baseStart_1293668 baseEnd_1293668 := by
    simpa [prefixWord, tailWord_1293668, baseEnd_1293668] using wordTrace_append hprefix tailTrace_1293668
  have hstable : (prefixWord ++ tailWord_1293668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293668).length < 2 ^ (prefixWord ++ tailWord_1293668).sum := by decide
  have hdescent : baseEnd_1293668 < baseStart_1293668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293681 : List Nat := [1, 2, 2, 2, 1, 2, 2, 11]
def baseStart_1293681 : Nat := 118140960795 + 1293681 * 2 ^ 59
def prefixEnd_1293681 : Nat := 4983230072969 + 3 ^ 40 * 1293681 * 2
def baseEnd_1293681 : Nat := 24602969132935488919925

theorem tailTrace_1293681 : CollatzResearch.WordTrace tailWord_1293681 prefixEnd_1293681 24602969132935488919925 := by
  unfold tailWord_1293681
  simp only [CollatzResearch.WordTrace]
  refine ⟨47184422426222154969728897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31456281617481436646485931 47184422426222154969728897)
  ·
    refine ⟨35388316819666616227296673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47184422426222154969728897 35388316819666616227296673)
    ·
      refine ⟨26541237614749962170472505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35388316819666616227296673 26541237614749962170472505)
      ·
        refine ⟨19905928211062471627854379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26541237614749962170472505 19905928211062471627854379)
        ·
          refine ⟨29858892316593707441781569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19905928211062471627854379 29858892316593707441781569)
          ·
            refine ⟨22394169237445280581336177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29858892316593707441781569 22394169237445280581336177)
            ·
              refine ⟨16795626928083960436002133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22394169237445280581336177 16795626928083960436002133)
              ·
                refine ⟨24602969132935488919925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 16795626928083960436002133 24602969132935488919925)
                ·
                  rfl

theorem cell23_1293681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 11].length) (baseStart_1293681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293681 prefixEnd_1293681 := by exact prefixLift 1293681
  have htrace : WordTrace (prefixWord ++ tailWord_1293681) baseStart_1293681 baseEnd_1293681 := by
    simpa [prefixWord, tailWord_1293681, baseEnd_1293681] using wordTrace_append hprefix tailTrace_1293681
  have hstable : (prefixWord ++ tailWord_1293681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293681).length < 2 ^ (prefixWord ++ tailWord_1293681).sum := by decide
  have hdescent : baseEnd_1293681 < baseStart_1293681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293752 : List Nat := [2, 1, 2, 1, 2, 2, 4, 3, 1, 3, 2]
def baseStart_1293752 : Nat := 118140960795 + 1293752 * 2 ^ 59
def prefixEnd_1293752 : Nat := 4983230072969 + 3 ^ 40 * 1293752 * 2
def baseEnd_1293752 : Nat := 664316623715727423050149

theorem tailTrace_1293752 : CollatzResearch.WordTrace tailWord_1293752 prefixEnd_1293752 664316623715727423050149 := by
  unfold tailWord_1293752
  simp only [CollatzResearch.WordTrace]
  refine ⟨23593506004482467047781755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31458008005976622730375673 23593506004482467047781755)
  ·
    refine ⟨35390259006723700571672633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23593506004482467047781755 35390259006723700571672633)
    ·
      refine ⟨26542694255042775428754475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35390259006723700571672633 26542694255042775428754475)
      ·
        refine ⟨39814041382564163143131713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26542694255042775428754475 39814041382564163143131713)
        ·
          refine ⟨29860531036923122357348785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39814041382564163143131713 29860531036923122357348785)
          ·
            refine ⟨22395398277692341768011589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29860531036923122357348785 22395398277692341768011589)
            ·
              refine ⟨4199137177067314081502173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22395398277692341768011589 4199137177067314081502173)
              ·
                refine ⟨1574676441400242780563315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4199137177067314081502173 1574676441400242780563315)
                ·
                  refine ⟨2362014662100364170844973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1574676441400242780563315 2362014662100364170844973)
                  ·
                    refine ⟨885755498287636564066865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2362014662100364170844973 885755498287636564066865)
                    ·
                      refine ⟨664316623715727423050149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 885755498287636564066865 664316623715727423050149)
                      ·
                        rfl

theorem cell23_1293752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 1, 3, 2].length) (baseStart_1293752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293752 prefixEnd_1293752 := by exact prefixLift 1293752
  have htrace : WordTrace (prefixWord ++ tailWord_1293752) baseStart_1293752 baseEnd_1293752 := by
    simpa [prefixWord, tailWord_1293752, baseEnd_1293752] using wordTrace_append hprefix tailTrace_1293752
  have hstable : (prefixWord ++ tailWord_1293752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293752).length < 2 ^ (prefixWord ++ tailWord_1293752).sum := by decide
  have hdescent : baseEnd_1293752 < baseStart_1293752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293768 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 1, 3, 5]
def baseStart_1293768 : Nat := 118140960795 + 1293768 * 2 ^ 59
def prefixEnd_1293768 : Nat := 4983230072969 + 3 ^ 40 * 1293768 * 2
def baseEnd_1293768 : Nat := 664324839406199360450075

theorem tailTrace_1293768 : CollatzResearch.WordTrace tailWord_1293768 prefixEnd_1293768 664324839406199360450075 := by
  unfold tailWord_1293768
  simp only [CollatzResearch.WordTrace]
  refine ⟨23593797788453484414072979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31458397051271312552097305 23593797788453484414072979)
  ·
    refine ⟨35390696682680226621109469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23593797788453484414072979 35390696682680226621109469)
    ·
      refine ⟨13271511256005084982916051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35390696682680226621109469 13271511256005084982916051)
      ·
        refine ⟨19907266884007627474374077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13271511256005084982916051 19907266884007627474374077)
        ·
          refine ⟨7465225081502860302890279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19907266884007627474374077 7465225081502860302890279)
          ·
            refine ⟨11197837622254290454335419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7465225081502860302890279 11197837622254290454335419)
            ·
              refine ⟨16796756433381435681503129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11197837622254290454335419 16796756433381435681503129)
              ·
                refine ⟨12597567325036076761127347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16796756433381435681503129 12597567325036076761127347)
                ·
                  refine ⟨18896350987554115141691021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12597567325036076761127347 18896350987554115141691021)
                  ·
                    refine ⟨7086131620332793178134133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18896350987554115141691021 7086131620332793178134133)
                    ·
                      refine ⟨664324839406199360450075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7086131620332793178134133 664324839406199360450075)
                      ·
                        rfl

theorem cell23_1293768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_1293768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293768 prefixEnd_1293768 := by exact prefixLift 1293768
  have htrace : WordTrace (prefixWord ++ tailWord_1293768) baseStart_1293768 baseEnd_1293768 := by
    simpa [prefixWord, tailWord_1293768, baseEnd_1293768] using wordTrace_append hprefix tailTrace_1293768
  have hstable : (prefixWord ++ tailWord_1293768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293768).length < 2 ^ (prefixWord ++ tailWord_1293768).sum := by decide
  have hdescent : baseEnd_1293768 < baseStart_1293768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293854 : List Nat := [4, 3, 3, 1, 2, 1, 2, 1, 1, 3, 2]
def baseStart_1293854 : Nat := 118140960795 + 1293854 * 2 ^ 59
def prefixEnd_1293854 : Nat := 4983230072969 + 3 ^ 40 * 1293854 * 2
def baseEnd_1293854 : Nat := 664368998742486023974681

theorem tailTrace_1293854 : CollatzResearch.WordTrace tailWord_1293854 prefixEnd_1293854 664368998742486023974681 := by
  unfold tailWord_1293854
  simp only [CollatzResearch.WordTrace]
  refine ⟨5898841531824425689472077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31460488169730270343851077 5898841531824425689472077)
  ·
    refine ⟨2212065574434159633552029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5898841531824425689472077 2212065574434159633552029)
    ·
      refine ⟨829524590412809862582011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2212065574434159633552029 829524590412809862582011)
      ·
        refine ⟨1244286885619214793873017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 829524590412809862582011 1244286885619214793873017)
        ·
          refine ⟨933215164214411095404763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1244286885619214793873017 933215164214411095404763)
          ·
            refine ⟨1399822746321616643107145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 933215164214411095404763 1399822746321616643107145)
            ·
              refine ⟨1049867059741212482330359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1399822746321616643107145 1049867059741212482330359)
              ·
                refine ⟨1574800589611818723495539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1049867059741212482330359 1574800589611818723495539)
                ·
                  refine ⟨2362200884417728085243309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1574800589611818723495539 2362200884417728085243309)
                  ·
                    refine ⟨885825331656648031966241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2362200884417728085243309 885825331656648031966241)
                    ·
                      refine ⟨664368998742486023974681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 885825331656648031966241 664368998742486023974681)
                      ·
                        rfl

theorem cell23_1293854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_1293854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293854 prefixEnd_1293854 := by exact prefixLift 1293854
  have htrace : WordTrace (prefixWord ++ tailWord_1293854) baseStart_1293854 baseEnd_1293854 := by
    simpa [prefixWord, tailWord_1293854, baseEnd_1293854] using wordTrace_append hprefix tailTrace_1293854
  have hstable : (prefixWord ++ tailWord_1293854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293854).length < 2 ^ (prefixWord ++ tailWord_1293854).sum := by decide
  have hdescent : baseEnd_1293854 < baseStart_1293854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293882 : List Nat := [3, 1, 1, 1, 3, 2, 4, 1, 3, 4]
def baseStart_1293882 : Nat := 118140960795 + 1293882 * 2 ^ 59
def prefixEnd_1293882 : Nat := 4983230072969 + 3 ^ 40 * 1293882 * 2
def baseEnd_1293882 : Nat := 221461125400270638141517

theorem tailTrace_1293882 : CollatzResearch.WordTrace tailWord_1293882 prefixEnd_1293882 221461125400270638141517 := by
  unfold tailWord_1293882
  simp only [CollatzResearch.WordTrace]
  refine ⟨11797938374623491574448975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31461168998995977531863933 11797938374623491574448975)
  ·
    refine ⟨17696907561935237361673463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11797938374623491574448975 17696907561935237361673463)
    ·
      refine ⟨26545361342902856042510195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17696907561935237361673463 26545361342902856042510195)
      ·
        refine ⟨39818042014354284063765293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26545361342902856042510195 39818042014354284063765293)
        ·
          refine ⟨14931765755382856523911985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39818042014354284063765293 14931765755382856523911985)
          ·
            refine ⟨11198824316537142392933989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14931765755382856523911985 11198824316537142392933989)
            ·
              refine ⟨2099779559350714198675123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11198824316537142392933989 2099779559350714198675123)
              ·
                refine ⟨3149669339026071298012685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2099779559350714198675123 3149669339026071298012685)
                ·
                  refine ⟨1181126002134776736754757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3149669339026071298012685 1181126002134776736754757)
                  ·
                    refine ⟨221461125400270638141517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1181126002134776736754757 221461125400270638141517)
                    ·
                      rfl

theorem cell23_1293882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 3, 4].length) (baseStart_1293882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293882 prefixEnd_1293882 := by exact prefixLift 1293882
  have htrace : WordTrace (prefixWord ++ tailWord_1293882) baseStart_1293882 baseEnd_1293882 := by
    simpa [prefixWord, tailWord_1293882, baseEnd_1293882] using wordTrace_append hprefix tailTrace_1293882
  have hstable : (prefixWord ++ tailWord_1293882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293882).length < 2 ^ (prefixWord ++ tailWord_1293882).sum := by decide
  have hdescent : baseEnd_1293882 < baseStart_1293882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293905 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 2, 5, 3]
def baseStart_1293905 : Nat := 118140960795 + 1293905 * 2 ^ 59
def prefixEnd_1293905 : Nat := 4983230072969 + 3 ^ 40 * 1293905 * 2
def baseEnd_1293905 : Nat := 664395186255865324436945

theorem tailTrace_1293905 : CollatzResearch.WordTrace tailWord_1293905 prefixEnd_1293905 664395186255865324436945 := by
  unfold tailWord_1293905
  simp only [CollatzResearch.WordTrace]
  refine ⟨47192592377410641225883169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31461728251607094150588779 47192592377410641225883169)
  ·
    refine ⟨35394444283057980919412377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47192592377410641225883169 35394444283057980919412377)
    ·
      refine ⟨26545833212293485689559283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35394444283057980919412377 26545833212293485689559283)
      ·
        refine ⟨39818749818440228534338925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26545833212293485689559283 39818749818440228534338925)
        ·
          refine ⟨14932031181915085700377097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39818749818440228534338925 14932031181915085700377097)
          ·
            refine ⟨11199023386436314275282823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14932031181915085700377097 11199023386436314275282823)
            ·
              refine ⟨16798535079654471412924235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11199023386436314275282823 16798535079654471412924235)
              ·
                refine ⟨25197802619481707119386353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16798535079654471412924235 25197802619481707119386353)
                ·
                  refine ⟨18898351964611280339539765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25197802619481707119386353 18898351964611280339539765)
                  ·
                    refine ⟨1771720496682307531831853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18898351964611280339539765 1771720496682307531831853)
                    ·
                      refine ⟨664395186255865324436945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1771720496682307531831853 664395186255865324436945)
                      ·
                        rfl

theorem cell23_1293905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 5, 3].length) (baseStart_1293905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293905 prefixEnd_1293905 := by exact prefixLift 1293905
  have htrace : WordTrace (prefixWord ++ tailWord_1293905) baseStart_1293905 baseEnd_1293905 := by
    simpa [prefixWord, tailWord_1293905, baseEnd_1293905] using wordTrace_append hprefix tailTrace_1293905
  have hstable : (prefixWord ++ tailWord_1293905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293905).length < 2 ^ (prefixWord ++ tailWord_1293905).sum := by decide
  have hdescent : baseEnd_1293905 < baseStart_1293905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293916 : List Nat := [2, 2, 4, 1, 2, 1, 3, 3, 1, 4]
def baseStart_1293916 : Nat := 118140960795 + 1293916 * 2 ^ 59
def prefixEnd_1293916 : Nat := 4983230072969 + 3 ^ 40 * 1293916 * 2
def baseEnd_1293916 : Nat := 221466944847688260466465

theorem tailTrace_1293916 : CollatzResearch.WordTrace tailWord_1293916 prefixEnd_1293916 221466944847688260466465 := by
  unfold tailWord_1293916
  simp only [CollatzResearch.WordTrace]
  refine ⟨23596496790185395052266801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31461995720247193403022401 23596496790185395052266801)
  ·
    refine ⟨17697372592639046289200101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23596496790185395052266801 17697372592639046289200101)
    ·
      refine ⟨3318257361119821179225019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17697372592639046289200101 3318257361119821179225019)
      ·
        refine ⟨4977386041679731768837529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3318257361119821179225019 4977386041679731768837529)
        ·
          refine ⟨3733039531259798826628147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4977386041679731768837529 3733039531259798826628147)
          ·
            refine ⟨5599559296889698239942221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3733039531259798826628147 5599559296889698239942221)
            ·
              refine ⟨2099834736333636839978333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5599559296889698239942221 2099834736333636839978333)
              ·
                refine ⟨787438026125113814991875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2099834736333636839978333 787438026125113814991875)
                ·
                  refine ⟨1181157039187670722487813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 787438026125113814991875 1181157039187670722487813)
                  ·
                    refine ⟨221466944847688260466465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1181157039187670722487813 221466944847688260466465)
                    ·
                      rfl

theorem cell23_1293916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_1293916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293916 prefixEnd_1293916 := by exact prefixLift 1293916
  have htrace : WordTrace (prefixWord ++ tailWord_1293916) baseStart_1293916 baseEnd_1293916 := by
    simpa [prefixWord, tailWord_1293916, baseEnd_1293916] using wordTrace_append hprefix tailTrace_1293916
  have hstable : (prefixWord ++ tailWord_1293916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293916).length < 2 ^ (prefixWord ++ tailWord_1293916).sum := by decide
  have hdescent : baseEnd_1293916 < baseStart_1293916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293933 : List Nat := [1, 5, 1, 1, 4, 1, 3, 2, 1, 4]
def baseStart_1293933 : Nat := 118140960795 + 1293933 * 2 ^ 59
def prefixEnd_1293933 : Nat := 4983230072969 + 3 ^ 40 * 1293933 * 2
def baseEnd_1293933 : Nat := 221469854571397071628939

theorem tailTrace_1293933 : CollatzResearch.WordTrace tailWord_1293933 prefixEnd_1293933 221469854571397071628939 := by
  unfold tailWord_1293933
  simp only [CollatzResearch.WordTrace]
  refine ⟨47193613621309202007902453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31462409080872801338601635 47193613621309202007902453)
  ·
    refine ⟨4424401276997737688240855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47193613621309202007902453 4424401276997737688240855)
    ·
      refine ⟨6636601915496606532361283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4424401276997737688240855 6636601915496606532361283)
      ·
        refine ⟨9954902873244909798541925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6636601915496606532361283 9954902873244909798541925)
        ·
          refine ⟨1866544288733420587226611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9954902873244909798541925 1866544288733420587226611)
          ·
            refine ⟨2799816433100130880839917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1866544288733420587226611 2799816433100130880839917)
            ·
              refine ⟨1049931162412549080314969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2799816433100130880839917 1049931162412549080314969)
              ·
                refine ⟨787448371809411810236227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1049931162412549080314969 787448371809411810236227)
                ·
                  refine ⟨1181172557714117715354341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 787448371809411810236227 1181172557714117715354341)
                  ·
                    refine ⟨221469854571397071628939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1181172557714117715354341 221469854571397071628939)
                    ·
                      rfl

theorem cell23_1293933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_1293933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293933 prefixEnd_1293933 := by exact prefixLift 1293933
  have htrace : WordTrace (prefixWord ++ tailWord_1293933) baseStart_1293933 baseEnd_1293933 := by
    simpa [prefixWord, tailWord_1293933, baseEnd_1293933] using wordTrace_append hprefix tailTrace_1293933
  have hstable : (prefixWord ++ tailWord_1293933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293933).length < 2 ^ (prefixWord ++ tailWord_1293933).sum := by decide
  have hdescent : baseEnd_1293933 < baseStart_1293933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293955 : List Nat := [1, 1, 1, 3, 3, 1, 1, 5, 1, 6]
def baseStart_1293955 : Nat := 118140960795 + 1293955 * 2 ^ 59
def prefixEnd_1293955 : Nat := 4983230072969 + 3 ^ 40 * 1293955 * 2
def baseEnd_1293955 : Nat := 221473620096196709603905

theorem tailTrace_1293955 : CollatzResearch.WordTrace tailWord_1293955 prefixEnd_1293955 221473620096196709603905 := by
  unfold tailWord_1293955
  simp only [CollatzResearch.WordTrace]
  refine ⟨47194416027229499765203319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31462944018152999843468879 47194416027229499765203319)
  ·
    refine ⟨70791624040844249647804979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47194416027229499765203319 70791624040844249647804979)
    ·
      refine ⟨106187436061266374471707469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70791624040844249647804979 106187436061266374471707469)
      ·
        refine ⟨39820288522974890426890301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106187436061266374471707469 39820288522974890426890301)
        ·
          refine ⟨14932608196115583910083863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39820288522974890426890301 14932608196115583910083863)
          ·
            refine ⟨22398912294173375865125795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14932608196115583910083863 22398912294173375865125795)
            ·
              refine ⟨33598368441260063797688693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22398912294173375865125795 33598368441260063797688693)
              ·
                refine ⟨3149847041368130981033315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33598368441260063797688693 3149847041368130981033315)
                ·
                  refine ⟨4724770562052196471549973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3149847041368130981033315 4724770562052196471549973)
                  ·
                    refine ⟨221473620096196709603905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4724770562052196471549973 221473620096196709603905)
                    ·
                      rfl

theorem cell23_1293955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 6].length) (baseStart_1293955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293955 prefixEnd_1293955 := by exact prefixLift 1293955
  have htrace : WordTrace (prefixWord ++ tailWord_1293955) baseStart_1293955 baseEnd_1293955 := by
    simpa [prefixWord, tailWord_1293955, baseEnd_1293955] using wordTrace_append hprefix tailTrace_1293955
  have hstable : (prefixWord ++ tailWord_1293955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293955).length < 2 ^ (prefixWord ++ tailWord_1293955).sum := by decide
  have hdescent : baseEnd_1293955 < baseStart_1293955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293959 : List Nat := [1, 1, 4, 2, 1, 5, 1, 2, 1, 5]
def baseStart_1293959 : Nat := 118140960795 + 1293959 * 2 ^ 59
def prefixEnd_1293959 : Nat := 4983230072969 + 3 ^ 40 * 1293959 * 2
def baseEnd_1293959 : Nat := 221474304737069371053899

theorem tailTrace_1293959 : CollatzResearch.WordTrace tailWord_1293959 prefixEnd_1293959 221474304737069371053899 := by
  unfold tailWord_1293959
  simp only [CollatzResearch.WordTrace]
  refine ⟨47194561919215008448348931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31463041279476672298899287 47194561919215008448348931)
  ·
    refine ⟨70791842878822512672523397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47194561919215008448348931 70791842878822512672523397)
    ·
      refine ⟨13273470539779221126098137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70791842878822512672523397 13273470539779221126098137)
      ·
        refine ⟨9955102904834415844573603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13273470539779221126098137 9955102904834415844573603)
        ·
          refine ⟨14932654357251623766860405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9955102904834415844573603 14932654357251623766860405)
          ·
            refine ⟨1399936345992339728143163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14932654357251623766860405 1399936345992339728143163)
            ·
              refine ⟨2099904518988509592214745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1399936345992339728143163 2099904518988509592214745)
              ·
                refine ⟨1574928389241382194161059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2099904518988509592214745 1574928389241382194161059)
                ·
                  refine ⟨2362392583862073291241589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1574928389241382194161059 2362392583862073291241589)
                  ·
                    refine ⟨221474304737069371053899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2362392583862073291241589 221474304737069371053899)
                    ·
                      rfl

theorem cell23_1293959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_1293959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293959 prefixEnd_1293959 := by exact prefixLift 1293959
  have htrace : WordTrace (prefixWord ++ tailWord_1293959) baseStart_1293959 baseEnd_1293959 := by
    simpa [prefixWord, tailWord_1293959, baseEnd_1293959] using wordTrace_append hprefix tailTrace_1293959
  have hstable : (prefixWord ++ tailWord_1293959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293959).length < 2 ^ (prefixWord ++ tailWord_1293959).sum := by decide
  have hdescent : baseEnd_1293959 < baseStart_1293959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293966 : List Nat := [4, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2]
def baseStart_1293966 : Nat := 118140960795 + 1293966 * 2 ^ 59
def prefixEnd_1293966 : Nat := 4983230072969 + 3 ^ 40 * 1293966 * 2
def baseEnd_1293966 : Nat := 664426508575789585774165

theorem tailTrace_1293966 : CollatzResearch.WordTrace tailWord_1293966 prefixEnd_1293966 664426508575789585774165 := by
  unfold tailWord_1293966
  simp only [CollatzResearch.WordTrace]
  refine ⟨5899352153773706080481719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31463211486793099095902501 5899352153773706080481719)
  ·
    refine ⟨8849028230660559120722579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5899352153773706080481719 8849028230660559120722579)
    ·
      refine ⟨13273542345990838681083869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8849028230660559120722579 13273542345990838681083869)
      ·
        refine ⟨4977578379746564505406451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13273542345990838681083869 4977578379746564505406451)
        ·
          refine ⟨7466367569619846758109677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4977578379746564505406451 7466367569619846758109677)
          ·
            refine ⟨2799887838607442534291129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7466367569619846758109677 2799887838607442534291129)
            ·
              refine ⟨2099915878955581900718347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2799887838607442534291129 2099915878955581900718347)
              ·
                refine ⟨3149873818433372851077521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2099915878955581900718347 3149873818433372851077521)
                ·
                  refine ⟨2362405363825029638308141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3149873818433372851077521 2362405363825029638308141)
                  ·
                    refine ⟨885902011434386114365553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2362405363825029638308141 885902011434386114365553)
                    ·
                      refine ⟨664426508575789585774165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 885902011434386114365553 664426508575789585774165)
                      ·
                        rfl

theorem cell23_1293966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_1293966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293966 prefixEnd_1293966 := by exact prefixLift 1293966
  have htrace : WordTrace (prefixWord ++ tailWord_1293966) baseStart_1293966 baseEnd_1293966 := by
    simpa [prefixWord, tailWord_1293966, baseEnd_1293966] using wordTrace_append hprefix tailTrace_1293966
  have hstable : (prefixWord ++ tailWord_1293966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293966).length < 2 ^ (prefixWord ++ tailWord_1293966).sum := by decide
  have hdescent : baseEnd_1293966 < baseStart_1293966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293985 : List Nat := [1, 2, 3, 3, 2, 12]
def baseStart_1293985 : Nat := 118140960795 + 1293985 * 2 ^ 59
def prefixEnd_1293985 : Nat := 4983230072969 + 3 ^ 40 * 1293985 * 2
def baseEnd_1293985 : Nat := 2734305616083230499739

theorem tailTrace_1293985 : CollatzResearch.WordTrace tailWord_1293985 prefixEnd_1293985 2734305616083230499739 := by
  unfold tailWord_1293985
  simp only [CollatzResearch.WordTrace]
  refine ⟨47195510217120814888795409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31463673478080543259196939 47195510217120814888795409)
  ·
    refine ⟨35396632662840611166596557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47195510217120814888795409 35396632662840611166596557)
    ·
      refine ⟨13273737248565229187473709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35396632662840611166596557 13273737248565229187473709)
      ·
        refine ⟨4977651468211960945302641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13273737248565229187473709 4977651468211960945302641)
        ·
          refine ⟨3733238601158970708976981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4977651468211960945302641 3733238601158970708976981)
          ·
            refine ⟨2734305616083230499739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 3733238601158970708976981 2734305616083230499739)
            ·
              rfl

theorem cell23_1293985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 12].length) (baseStart_1293985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1293985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1293985 prefixEnd_1293985 := by exact prefixLift 1293985
  have htrace : WordTrace (prefixWord ++ tailWord_1293985) baseStart_1293985 baseEnd_1293985 := by
    simpa [prefixWord, tailWord_1293985, baseEnd_1293985] using wordTrace_append hprefix tailTrace_1293985
  have hstable : (prefixWord ++ tailWord_1293985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293985).length < 2 ^ (prefixWord ++ tailWord_1293985).sum := by decide
  have hdescent : baseEnd_1293985 < baseStart_1293985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294006 : List Nat := [5, 1, 3, 1, 1, 2, 2, 1, 1, 6]
def baseStart_1294006 : Nat := 118140960795 + 1294006 * 2 ^ 59
def prefixEnd_1294006 : Nat := 4983230072969 + 3 ^ 40 * 1294006 * 2
def baseEnd_1294006 : Nat := 221482349267323143091327

theorem tailTrace_1294006 : CollatzResearch.WordTrace tailWord_1294006 prefixEnd_1294006 221482349267323143091327 := by
  unfold tailWord_1294006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2949767259377795967206867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31464184100029823650206581 2949767259377795967206867)
  ·
    refine ⟨4424650889066693950810301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2949767259377795967206867 4424650889066693950810301)
    ·
      refine ⟨1659244083400010231553863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4424650889066693950810301 1659244083400010231553863)
      ·
        refine ⟨2488866125100015347330795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1659244083400010231553863 2488866125100015347330795)
        ·
          refine ⟨3733299187650023020996193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2488866125100015347330795 3733299187650023020996193)
          ·
            refine ⟨2799974390737517265747145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3733299187650023020996193 2799974390737517265747145)
            ·
              refine ⟨2099980793053137949310359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2799974390737517265747145 2099980793053137949310359)
              ·
                refine ⟨3149971189579706923965539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2099980793053137949310359 3149971189579706923965539)
                ·
                  refine ⟨4724956784369560385948309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3149971189579706923965539 4724956784369560385948309)
                  ·
                    refine ⟨221482349267323143091327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4724956784369560385948309 221482349267323143091327)
                    ·
                      rfl

theorem cell23_1294006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_1294006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294006 prefixEnd_1294006 := by exact prefixLift 1294006
  have htrace : WordTrace (prefixWord ++ tailWord_1294006) baseStart_1294006 baseEnd_1294006 := by
    simpa [prefixWord, tailWord_1294006, baseEnd_1294006] using wordTrace_append hprefix tailTrace_1294006
  have hstable : (prefixWord ++ tailWord_1294006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294006).length < 2 ^ (prefixWord ++ tailWord_1294006).sum := by decide
  have hdescent : baseEnd_1294006 < baseStart_1294006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294015 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 2, 7]
def baseStart_1294015 : Nat := 118140960795 + 1294015 * 2 ^ 59
def prefixEnd_1294015 : Nat := 4983230072969 + 3 ^ 40 * 1294015 * 2
def baseEnd_1294015 : Nat := 221483889709286631353813

theorem tailTrace_1294015 : CollatzResearch.WordTrace tailWord_1294015 prefixEnd_1294015 221483889709286631353813 := by
  unfold tailWord_1294015
  simp only [CollatzResearch.WordTrace]
  refine ⟨47196604407012130012387499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31464402938008086674924999 47196604407012130012387499)
  ·
    refine ⟨70794906610518195018581249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47196604407012130012387499 70794906610518195018581249)
    ·
      refine ⟨53096179957888646263935937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70794906610518195018581249 53096179957888646263935937)
      ·
        refine ⟨39822134968416484697951953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53096179957888646263935937 39822134968416484697951953)
        ·
          refine ⟨29866601226312363523463965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39822134968416484697951953 29866601226312363523463965)
          ·
            refine ⟨11199975459867136321298987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29866601226312363523463965 11199975459867136321298987)
            ·
              refine ⟨16799963189800704481948481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11199975459867136321298987 16799963189800704481948481)
              ·
                refine ⟨12599972392350528361461361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16799963189800704481948481 12599972392350528361461361)
                ·
                  refine ⟨9449979294262896271096021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12599972392350528361461361 9449979294262896271096021)
                  ·
                    refine ⟨221483889709286631353813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9449979294262896271096021 221483889709286631353813)
                    ·
                      rfl

theorem cell23_1294015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 7].length) (baseStart_1294015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294015 prefixEnd_1294015 := by exact prefixLift 1294015
  have htrace : WordTrace (prefixWord ++ tailWord_1294015) baseStart_1294015 baseEnd_1294015 := by
    simpa [prefixWord, tailWord_1294015, baseEnd_1294015] using wordTrace_append hprefix tailTrace_1294015
  have hstable : (prefixWord ++ tailWord_1294015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294015).length < 2 ^ (prefixWord ++ tailWord_1294015).sum := by decide
  have hdescent : baseEnd_1294015 < baseStart_1294015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294062 : List Nat := [4, 1, 2, 1, 1, 2, 1, 3, 2, 6]
def baseStart_1294062 : Nat := 118140960795 + 1294062 * 2 ^ 59
def prefixEnd_1294062 : Nat := 4983230072969 + 3 ^ 40 * 1294062 * 2
def baseEnd_1294062 : Nat := 221491934239540403391241

theorem tailTrace_1294062 : CollatzResearch.WordTrace tailWord_1294062 prefixEnd_1294062 221491934239540403391241 := by
  unfold tailWord_1294062
  simp only [CollatzResearch.WordTrace]
  refine ⟨5899789829730232129918555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31465545758561238026232293 5899789829730232129918555)
  ·
    refine ⟨8849684744595348194877833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5899789829730232129918555 8849684744595348194877833)
    ·
      refine ⟨6637263558446511146158375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8849684744595348194877833 6637263558446511146158375)
      ·
        refine ⟨9955895337669766719237563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6637263558446511146158375 9955895337669766719237563)
        ·
          refine ⟨14933843006504650078856345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9955895337669766719237563 14933843006504650078856345)
          ·
            refine ⟨11200382254878487559142259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14933843006504650078856345 11200382254878487559142259)
            ·
              refine ⟨16800573382317731338713389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11200382254878487559142259 16800573382317731338713389)
              ·
                refine ⟨6300215018369149252017521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16800573382317731338713389 6300215018369149252017521)
                ·
                  refine ⟨4725161263776861939013141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6300215018369149252017521 4725161263776861939013141)
                  ·
                    refine ⟨221491934239540403391241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4725161263776861939013141 221491934239540403391241)
                    ·
                      rfl

theorem cell23_1294062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_1294062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294062 prefixEnd_1294062 := by exact prefixLift 1294062
  have htrace : WordTrace (prefixWord ++ tailWord_1294062) baseStart_1294062 baseEnd_1294062 := by
    simpa [prefixWord, tailWord_1294062, baseEnd_1294062] using wordTrace_append hprefix tailTrace_1294062
  have hstable : (prefixWord ++ tailWord_1294062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294062).length < 2 ^ (prefixWord ++ tailWord_1294062).sum := by decide
  have hdescent : baseEnd_1294062 < baseStart_1294062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294075 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 9]
def baseStart_1294075 : Nat := 118140960795 + 1294075 * 2 ^ 59
def prefixEnd_1294075 : Nat := 4983230072969 + 3 ^ 40 * 1294075 * 2
def baseEnd_1294075 : Nat := 73831386440792184367907

theorem tailTrace_1294075 : CollatzResearch.WordTrace tailWord_1294075 prefixEnd_1294075 73831386440792184367907 := by
  unfold tailWord_1294075
  simp only [CollatzResearch.WordTrace]
  refine ⟨47198792786794760259571679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31465861857863173506381119 47198792786794760259571679)
  ·
    refine ⟨70798189180192140389357519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47198792786794760259571679 70798189180192140389357519)
    ·
      refine ⟨106197283770288210584036279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70798189180192140389357519 106197283770288210584036279)
      ·
        refine ⟨159295925655432315876054419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106197283770288210584036279 159295925655432315876054419)
        ·
          refine ⟨238943888483148473814081629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159295925655432315876054419 238943888483148473814081629)
          ·
            refine ⟨89603958181180677680280611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 238943888483148473814081629 89603958181180677680280611)
            ·
              refine ⟨134405937271771016520420917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89603958181180677680280611 134405937271771016520420917)
              ·
                refine ⟨12600556619228532798789461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 134405937271771016520420917 12600556619228532798789461)
                ·
                  refine ⟨73831386440792184367907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12600556619228532798789461 73831386440792184367907)
                  ·
                    rfl

theorem cell23_1294075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 9].length) (baseStart_1294075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294075 prefixEnd_1294075 := by exact prefixLift 1294075
  have htrace : WordTrace (prefixWord ++ tailWord_1294075) baseStart_1294075 baseEnd_1294075 := by
    simpa [prefixWord, tailWord_1294075, baseEnd_1294075] using wordTrace_append hprefix tailTrace_1294075
  have hstable : (prefixWord ++ tailWord_1294075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294075).length < 2 ^ (prefixWord ++ tailWord_1294075).sum := by decide
  have hdescent : baseEnd_1294075 < baseStart_1294075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294120 : List Nat := [2, 1, 5, 1, 1, 2, 4, 1, 2, 2, 2]
def baseStart_1294120 : Nat := 118140960795 + 1294120 * 2 ^ 59
def prefixEnd_1294120 : Nat := 4983230072969 + 3 ^ 40 * 1294120 * 2
def baseEnd_1294120 : Nat := 664505584596581983248457

theorem tailTrace_1294120 : CollatzResearch.WordTrace tailWord_1294120 prefixEnd_1294120 664505584596581983248457 := by
  unfold tailWord_1294120
  simp only [CollatzResearch.WordTrace]
  refine ⟨23600217035815866472479907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31466956047754488629973209 23600217035815866472479907)
  ·
    refine ⟨35400325553723799708719861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23600217035815866472479907 35400325553723799708719861)
    ·
      refine ⟨3318780520661606222692487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35400325553723799708719861 3318780520661606222692487)
      ·
        refine ⟨4978170780992409334038731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3318780520661606222692487 4978170780992409334038731)
        ·
          refine ⟨7467256171488614001058097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4978170780992409334038731 7467256171488614001058097)
          ·
            refine ⟨5600442128616460500793573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7467256171488614001058097 5600442128616460500793573)
            ·
              refine ⟨1050082899115586343898795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5600442128616460500793573 1050082899115586343898795)
              ·
                refine ⟨1575124348673379515848193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1050082899115586343898795 1575124348673379515848193)
                ·
                  refine ⟨1181343261505034636886145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1575124348673379515848193 1181343261505034636886145)
                  ·
                    refine ⟨886007446128775977664609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1181343261505034636886145 886007446128775977664609)
                    ·
                      refine ⟨664505584596581983248457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 886007446128775977664609 664505584596581983248457)
                      ·
                        rfl

theorem cell23_1294120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_1294120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294120 prefixEnd_1294120 := by exact prefixLift 1294120
  have htrace : WordTrace (prefixWord ++ tailWord_1294120) baseStart_1294120 baseEnd_1294120 := by
    simpa [prefixWord, tailWord_1294120, baseEnd_1294120] using wordTrace_append hprefix tailTrace_1294120
  have hstable : (prefixWord ++ tailWord_1294120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294120).length < 2 ^ (prefixWord ++ tailWord_1294120).sum := by decide
  have hdescent : baseEnd_1294120 < baseStart_1294120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294169 : List Nat := [1, 2, 1, 2, 2, 3, 2, 3, 3, 4]
def baseStart_1294169 : Nat := 118140960795 + 1294169 * 2 ^ 59
def prefixEnd_1294169 : Nat := 4983230072969 + 3 ^ 40 * 1294169 * 2
def baseEnd_1294169 : Nat := 221510248382884097178577

theorem tailTrace_1294169 : CollatzResearch.WordTrace tailWord_1294169 prefixEnd_1294169 221510248382884097178577 := by
  unfold tailWord_1294169
  simp only [CollatzResearch.WordTrace]
  refine ⟨47202221248454214313493561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31468147498969476208995707 47202221248454214313493561)
  ·
    refine ⟨35401665936340660735120171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47202221248454214313493561 35401665936340660735120171)
    ·
      refine ⟨53102498904510991102680257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35401665936340660735120171 53102498904510991102680257)
      ·
        refine ⟨39826874178383243327010193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53102498904510991102680257 39826874178383243327010193)
        ·
          refine ⟨29870155633787432495257645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39826874178383243327010193 29870155633787432495257645)
          ·
            refine ⟨11201308362670287185721617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29870155633787432495257645 11201308362670287185721617)
            ·
              refine ⟨8400981272002715389291213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11201308362670287185721617 8400981272002715389291213)
              ·
                refine ⟨3150367977001018270984205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8400981272002715389291213 3150367977001018270984205)
                ·
                  refine ⟨1181387991375381851619077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3150367977001018270984205 1181387991375381851619077)
                  ·
                    refine ⟨221510248382884097178577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1181387991375381851619077 221510248382884097178577)
                    ·
                      rfl

theorem cell23_1294169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 4].length) (baseStart_1294169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294169 prefixEnd_1294169 := by exact prefixLift 1294169
  have htrace : WordTrace (prefixWord ++ tailWord_1294169) baseStart_1294169 baseEnd_1294169 := by
    simpa [prefixWord, tailWord_1294169, baseEnd_1294169] using wordTrace_append hprefix tailTrace_1294169
  have hstable : (prefixWord ++ tailWord_1294169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294169).length < 2 ^ (prefixWord ++ tailWord_1294169).sum := by decide
  have hdescent : baseEnd_1294169 < baseStart_1294169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294176 : List Nat := [2, 1, 1, 3, 3, 3, 1, 1, 2, 4, 2]
def baseStart_1294176 : Nat := 118140960795 + 1294176 * 2 ^ 59
def prefixEnd_1294176 : Nat := 4983230072969 + 3 ^ 40 * 1294176 * 2
def baseEnd_1294176 : Nat := 664534339513233764148199

theorem tailTrace_1294176 : CollatzResearch.WordTrace tailWord_1294176 prefixEnd_1294176 664534339513233764148199 := by
  unfold tailWord_1294176
  simp only [CollatzResearch.WordTrace]
  refine ⟨23601238279714427254499191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31468317706285903005998921 23601238279714427254499191)
  ·
    refine ⟨35401857419571640881748787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23601238279714427254499191 35401857419571640881748787)
    ·
      refine ⟨53102786129357461322623181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35401857419571640881748787 53102786129357461322623181)
      ·
        refine ⟨19913544798509047995983693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53102786129357461322623181 19913544798509047995983693)
        ·
          refine ⟨7467579299440892998493885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19913544798509047995983693 7467579299440892998493885)
          ·
            refine ⟨2800342237290334874435207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7467579299440892998493885 2800342237290334874435207)
            ·
              refine ⟨4200513355935502311652811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2800342237290334874435207 4200513355935502311652811)
              ·
                refine ⟨6300770033903253467479217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4200513355935502311652811 6300770033903253467479217)
                ·
                  refine ⟨4725577525427440100609413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6300770033903253467479217 4725577525427440100609413)
                  ·
                    refine ⟨886045786017645018864265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4725577525427440100609413 886045786017645018864265)
                    ·
                      refine ⟨664534339513233764148199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 886045786017645018864265 664534339513233764148199)
                      ·
                        rfl

theorem cell23_1294176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 2, 4, 2].length) (baseStart_1294176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294176 prefixEnd_1294176 := by exact prefixLift 1294176
  have htrace : WordTrace (prefixWord ++ tailWord_1294176) baseStart_1294176 baseEnd_1294176 := by
    simpa [prefixWord, tailWord_1294176, baseEnd_1294176] using wordTrace_append hprefix tailTrace_1294176
  have hstable : (prefixWord ++ tailWord_1294176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294176).length < 2 ^ (prefixWord ++ tailWord_1294176).sum := by decide
  have hdescent : baseEnd_1294176 < baseStart_1294176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294206 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_1294206 : Nat := 118140960795 + 1294206 * 2 ^ 59
def prefixEnd_1294206 : Nat := 4983230072969 + 3 ^ 40 * 1294206 * 2
def baseEnd_1294206 : Nat := 664549743932868646773061

theorem tailTrace_1294206 : CollatzResearch.WordTrace tailWord_1294206 prefixEnd_1294206 664549743932868646773061 := by
  unfold tailWord_1294206
  simp only [CollatzResearch.WordTrace]
  refine ⟨5900446343665021204073809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31469047166213446421726981 5900446343665021204073809)
  ·
    refine ⟨4425334757748765903055357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5900446343665021204073809 4425334757748765903055357)
    ·
      refine ⟨1659500534155787213645759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4425334757748765903055357 1659500534155787213645759)
      ·
        refine ⟨2489250801233680820468639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1659500534155787213645759 2489250801233680820468639)
        ·
          refine ⟨3733876201850521230702959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2489250801233680820468639 3733876201850521230702959)
          ·
            refine ⟨5600814302775781846054439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3733876201850521230702959 5600814302775781846054439)
            ·
              refine ⟨8401221454163672769081659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5600814302775781846054439 8401221454163672769081659)
              ·
                refine ⟨12601832181245509153622489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8401221454163672769081659 12601832181245509153622489)
                ·
                  refine ⟨9451374135934131865216867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12601832181245509153622489 9451374135934131865216867)
                  ·
                    refine ⟨14177061203901197797825301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9451374135934131865216867 14177061203901197797825301)
                    ·
                      refine ⟨664549743932868646773061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14177061203901197797825301 664549743932868646773061)
                      ·
                        rfl

theorem cell23_1294206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_1294206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294206 prefixEnd_1294206 := by exact prefixLift 1294206
  have htrace : WordTrace (prefixWord ++ tailWord_1294206) baseStart_1294206 baseEnd_1294206 := by
    simpa [prefixWord, tailWord_1294206, baseEnd_1294206] using wordTrace_append hprefix tailTrace_1294206
  have hstable : (prefixWord ++ tailWord_1294206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294206).length < 2 ^ (prefixWord ++ tailWord_1294206).sum := by decide
  have hdescent : baseEnd_1294206 < baseStart_1294206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294259 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 6, 4]
def baseStart_1294259 : Nat := 118140960795 + 1294259 * 2 ^ 59
def prefixEnd_1294259 : Nat := 4983230072969 + 3 ^ 40 * 1294259 * 2
def baseEnd_1294259 : Nat := 221525652802518979803439

theorem tailTrace_1294259 : CollatzResearch.WordTrace tailWord_1294259 prefixEnd_1294259 221525652802518979803439 := by
  unfold tailWord_1294259
  simp only [CollatzResearch.WordTrace]
  refine ⟨47205503818128159684269831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31470335878752106456179887 47205503818128159684269831)
  ·
    refine ⟨70808255727192239526404747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47205503818128159684269831 70808255727192239526404747)
    ·
      refine ⟨106212383590788359289607121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70808255727192239526404747 106212383590788359289607121)
      ·
        refine ⟨79659287693091269467205341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106212383590788359289607121 79659287693091269467205341)
        ·
          refine ⟨29872232884909226050202003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79659287693091269467205341 29872232884909226050202003)
          ·
            refine ⟨44808349327363839075303005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29872232884909226050202003 44808349327363839075303005)
            ·
              refine ⟨16803130997761439653238627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44808349327363839075303005 16803130997761439653238627)
              ·
                refine ⟨25204696496642159479857941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16803130997761439653238627 25204696496642159479857941)
                ·
                  refine ⟨1181470148280101225618341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25204696496642159479857941 1181470148280101225618341)
                  ·
                    refine ⟨221525652802518979803439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1181470148280101225618341 221525652802518979803439)
                    ·
                      rfl

theorem cell23_1294259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6, 4].length) (baseStart_1294259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294259 prefixEnd_1294259 := by exact prefixLift 1294259
  have htrace : WordTrace (prefixWord ++ tailWord_1294259) baseStart_1294259 baseEnd_1294259 := by
    simpa [prefixWord, tailWord_1294259, baseEnd_1294259] using wordTrace_append hprefix tailTrace_1294259
  have hstable : (prefixWord ++ tailWord_1294259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294259).length < 2 ^ (prefixWord ++ tailWord_1294259).sum := by decide
  have hdescent : baseEnd_1294259 < baseStart_1294259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294286 : List Nat := [4, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3]
def baseStart_1294286 : Nat := 118140960795 + 1294286 * 2 ^ 59
def prefixEnd_1294286 : Nat := 4983230072969 + 3 ^ 40 * 1294286 * 2
def baseEnd_1294286 : Nat := 664590822385228333772693

theorem tailTrace_1294286 : CollatzResearch.WordTrace tailWord_1294286 prefixEnd_1294286 664590822385228333772693 := by
  unfold tailWord_1294286
  simp only [CollatzResearch.WordTrace]
  refine ⟨5900811073628792911937839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31470992392686895530335141 5900811073628792911937839)
  ·
    refine ⟨8851216610443189367906759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5900811073628792911937839 8851216610443189367906759)
    ·
      refine ⟨13276824915664784051860139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8851216610443189367906759 13276824915664784051860139)
      ·
        refine ⟨19915237373497176077790209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13276824915664784051860139 19915237373497176077790209)
        ·
          refine ⟨14936428030122882058342657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19915237373497176077790209 14936428030122882058342657)
          ·
            refine ⟨11202321022592161543756993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14936428030122882058342657 11202321022592161543756993)
            ·
              refine ⟨8401740766944121157817745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11202321022592161543756993 8401740766944121157817745)
              ·
                refine ⟨6301305575208090868363309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8401740766944121157817745 6301305575208090868363309)
                ·
                  refine ⟨2362989590703034075636241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6301305575208090868363309 2362989590703034075636241)
                  ·
                    refine ⟨1772242193027275556727181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2362989590703034075636241 1772242193027275556727181)
                    ·
                      refine ⟨664590822385228333772693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1772242193027275556727181 664590822385228333772693)
                      ·
                        rfl

theorem cell23_1294286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_1294286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294286 prefixEnd_1294286 := by exact prefixLift 1294286
  have htrace : WordTrace (prefixWord ++ tailWord_1294286) baseStart_1294286 baseEnd_1294286 := by
    simpa [prefixWord, tailWord_1294286, baseEnd_1294286] using wordTrace_append hprefix tailTrace_1294286
  have hstable : (prefixWord ++ tailWord_1294286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294286).length < 2 ^ (prefixWord ++ tailWord_1294286).sum := by decide
  have hdescent : baseEnd_1294286 < baseStart_1294286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294293 : List Nat := [1, 3, 2, 3, 2, 2, 1, 3, 2, 4]
def baseStart_1294293 : Nat := 118140960795 + 1294293 * 2 ^ 59
def prefixEnd_1294293 : Nat := 4983230072969 + 3 ^ 40 * 1294293 * 2
def baseEnd_1294293 : Nat := 221531472249936602128387

theorem tailTrace_1294293 : CollatzResearch.WordTrace tailWord_1294293 prefixEnd_1294293 221531472249936602128387 := by
  unfold tailWord_1294293
  simp only [CollatzResearch.WordTrace]
  refine ⟨47206743900004983491007533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31471162600003322327338355 47206743900004983491007533)
  ·
    refine ⟨17702528962501868809127825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47206743900004983491007533 17702528962501868809127825)
    ·
      refine ⟨13276896721876401606845869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17702528962501868809127825 13276896721876401606845869)
      ·
        refine ⟨4978836270703650602567201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13276896721876401606845869 4978836270703650602567201)
        ·
          refine ⟨3734127203027737951925401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4978836270703650602567201 3734127203027737951925401)
          ·
            refine ⟨2800595402270803463944051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3734127203027737951925401 2800595402270803463944051)
            ·
              refine ⟨4200893103406205195916077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2800595402270803463944051 4200893103406205195916077)
              ·
                refine ⟨1575334913777326948468529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4200893103406205195916077 1575334913777326948468529)
                ·
                  refine ⟨1181501185332995211351397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1575334913777326948468529 1181501185332995211351397)
                  ·
                    refine ⟨221531472249936602128387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1181501185332995211351397 221531472249936602128387)
                    ·
                      rfl

theorem cell23_1294293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_1294293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294293 prefixEnd_1294293 := by exact prefixLift 1294293
  have htrace : WordTrace (prefixWord ++ tailWord_1294293) baseStart_1294293 baseEnd_1294293 := by
    simpa [prefixWord, tailWord_1294293, baseEnd_1294293] using wordTrace_append hprefix tailTrace_1294293
  have hstable : (prefixWord ++ tailWord_1294293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294293).length < 2 ^ (prefixWord ++ tailWord_1294293).sum := by decide
  have hdescent : baseEnd_1294293 < baseStart_1294293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294303 : List Nat := [1, 1, 2, 3, 4, 1, 3, 2, 1, 2, 3]
def baseStart_1294303 : Nat := 118140960795 + 1294303 * 2 ^ 59
def prefixEnd_1294303 : Nat := 4983230072969 + 3 ^ 40 * 1294303 * 2
def baseEnd_1294303 : Nat := 664599551556354767260115

theorem tailTrace_1294303 : CollatzResearch.WordTrace tailWord_1294303 prefixEnd_1294303 664599551556354767260115 := by
  unfold tailWord_1294303
  simp only [CollatzResearch.WordTrace]
  refine ⟨47207108629968755198871563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31471405753312503465914375 47207108629968755198871563)
  ·
    refine ⟨70810662944953132798307345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47207108629968755198871563 70810662944953132798307345)
    ·
      refine ⟨53107997208714849598730509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70810662944953132798307345 53107997208714849598730509)
      ·
        refine ⟨19915498953268068599523941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53107997208714849598730509 19915498953268068599523941)
        ·
          refine ⟨3734156053737762862410739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19915498953268068599523941 3734156053737762862410739)
          ·
            refine ⟨5601234080606644293616109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3734156053737762862410739 5601234080606644293616109)
            ·
              refine ⟨2100462780227491610106041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5601234080606644293616109 2100462780227491610106041)
              ·
                refine ⟨1575347085170618707579531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2100462780227491610106041 1575347085170618707579531)
                ·
                  refine ⟨2363020627755928061369297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1575347085170618707579531 2363020627755928061369297)
                  ·
                    refine ⟨1772265470816946046026973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2363020627755928061369297 1772265470816946046026973)
                    ·
                      refine ⟨664599551556354767260115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1772265470816946046026973 664599551556354767260115)
                      ·
                        rfl

theorem cell23_1294303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_1294303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294303 prefixEnd_1294303 := by exact prefixLift 1294303
  have htrace : WordTrace (prefixWord ++ tailWord_1294303) baseStart_1294303 baseEnd_1294303 := by
    simpa [prefixWord, tailWord_1294303, baseEnd_1294303] using wordTrace_append hprefix tailTrace_1294303
  have hstable : (prefixWord ++ tailWord_1294303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294303).length < 2 ^ (prefixWord ++ tailWord_1294303).sum := by decide
  have hdescent : baseEnd_1294303 < baseStart_1294303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294316 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 3]
def baseStart_1294316 : Nat := 118140960795 + 1294316 * 2 ^ 59
def prefixEnd_1294316 : Nat := 4983230072969 + 3 ^ 40 * 1294316 * 2
def baseEnd_1294316 : Nat := 664606226804863216397555

theorem tailTrace_1294316 : CollatzResearch.WordTrace tailWord_1294316 prefixEnd_1294316 664606226804863216397555 := by
  unfold tailWord_1294316
  simp only [CollatzResearch.WordTrace]
  refine ⟨23603791389460829209547401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31471721852614438946063201 23603791389460829209547401)
  ·
    refine ⟨17702843542095621907160551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23603791389460829209547401 17702843542095621907160551)
    ·
      refine ⟨26554265313143432860740827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17702843542095621907160551 26554265313143432860740827)
      ·
        refine ⟨39831397969715149291111241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26554265313143432860740827 39831397969715149291111241)
        ·
          refine ⟨29873548477286361968333431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39831397969715149291111241 29873548477286361968333431)
          ·
            refine ⟨44810322715929542952500147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29873548477286361968333431 44810322715929542952500147)
            ·
              refine ⟨67215484073894314428750221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44810322715929542952500147 67215484073894314428750221)
              ·
                refine ⟨25205806527710367910781333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67215484073894314428750221 25205806527710367910781333)
                ·
                  refine ⟨1181522180986423495817875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25205806527710367910781333 1181522180986423495817875)
                  ·
                    refine ⟨1772283271479635243726813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1181522180986423495817875 1772283271479635243726813)
                    ·
                      refine ⟨664606226804863216397555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1772283271479635243726813 664606226804863216397555)
                      ·
                        rfl

theorem cell23_1294316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 3].length) (baseStart_1294316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294316 prefixEnd_1294316 := by exact prefixLift 1294316
  have htrace : WordTrace (prefixWord ++ tailWord_1294316) baseStart_1294316 baseEnd_1294316 := by
    simpa [prefixWord, tailWord_1294316, baseEnd_1294316] using wordTrace_append hprefix tailTrace_1294316
  have hstable : (prefixWord ++ tailWord_1294316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294316).length < 2 ^ (prefixWord ++ tailWord_1294316).sum := by decide
  have hdescent : baseEnd_1294316 < baseStart_1294316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294317 : List Nat := [1, 5, 1, 4, 1, 1, 3, 1, 1, 1, 4]
def baseStart_1294317 : Nat := 118140960795 + 1294317 * 2 ^ 59
def prefixEnd_1294317 : Nat := 4983230072969 + 3 ^ 40 * 1294317 * 2
def baseEnd_1294317 : Nat := 664606740285517712485051

theorem tailTrace_1294317 : CollatzResearch.WordTrace tailWord_1294317 prefixEnd_1294317 664606740285517712485051 := by
  unfold tailWord_1294317
  simp only [CollatzResearch.WordTrace]
  refine ⟨47207619251918035589881205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31471746167945357059920803 47207619251918035589881205)
  ·
    refine ⟨4425714304867315836551363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47207619251918035589881205 4425714304867315836551363)
    ·
      refine ⟨6638571457300973754827045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4425714304867315836551363 6638571457300973754827045)
      ·
        refine ⟨1244732148243932579030071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6638571457300973754827045 1244732148243932579030071)
        ·
          refine ⟨1867098222365898868545107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1244732148243932579030071 1867098222365898868545107)
          ·
            refine ⟨2800647333548848302817661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1867098222365898868545107 2800647333548848302817661)
            ·
              refine ⟨1050242750080818113556623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2800647333548848302817661 1050242750080818113556623)
              ·
                refine ⟨1575364125121227170334935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1050242750080818113556623 1575364125121227170334935)
                ·
                  refine ⟨2363046187681840755502403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1575364125121227170334935 2363046187681840755502403)
                  ·
                    refine ⟨3544569281522761133253605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2363046187681840755502403 3544569281522761133253605)
                    ·
                      refine ⟨664606740285517712485051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3544569281522761133253605 664606740285517712485051)
                      ·
                        rfl

theorem cell23_1294317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_1294317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294317 prefixEnd_1294317 := by exact prefixLift 1294317
  have htrace : WordTrace (prefixWord ++ tailWord_1294317) baseStart_1294317 baseEnd_1294317 := by
    simpa [prefixWord, tailWord_1294317, baseEnd_1294317] using wordTrace_append hprefix tailTrace_1294317
  have hstable : (prefixWord ++ tailWord_1294317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294317).length < 2 ^ (prefixWord ++ tailWord_1294317).sum := by decide
  have hdescent : baseEnd_1294317 < baseStart_1294317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294333 : List Nat := [1, 4, 1, 1, 1, 2, 3, 4, 2, 1, 3]
def baseStart_1294333 : Nat := 118140960795 + 1294333 * 2 ^ 59
def prefixEnd_1294333 : Nat := 4983230072969 + 3 ^ 40 * 1294333 * 2
def baseEnd_1294333 : Nat := 664614955975989649884977

theorem tailTrace_1294333 : CollatzResearch.WordTrace tailWord_1294333 prefixEnd_1294333 664614955975989649884977 := by
  unfold tailWord_1294333
  simp only [CollatzResearch.WordTrace]
  refine ⟨47208202819860070322463653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31472135213240046881642435 47208202819860070322463653)
  ·
    refine ⟨8851538028723763185461935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47208202819860070322463653 8851538028723763185461935)
    ·
      refine ⟨13277307043085644778192903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8851538028723763185461935 13277307043085644778192903)
      ·
        refine ⟨19915960564628467167289355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13277307043085644778192903 19915960564628467167289355)
        ·
          refine ⟨29873940846942700750934033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19915960564628467167289355 29873940846942700750934033)
          ·
            refine ⟨22405455635207025563200525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29873940846942700750934033 22405455635207025563200525)
            ·
              refine ⟨8402045863202634586200197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22405455635207025563200525 8402045863202634586200197)
              ·
                refine ⟨1575383599350493984912537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8402045863202634586200197 1575383599350493984912537)
                ·
                  refine ⟨1181537699512870488684403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1575383599350493984912537 1181537699512870488684403)
                  ·
                    refine ⟨1772306549269305733026605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1181537699512870488684403 1772306549269305733026605)
                    ·
                      refine ⟨664614955975989649884977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1772306549269305733026605 664614955975989649884977)
                      ·
                        rfl

theorem cell23_1294333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_1294333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294333 prefixEnd_1294333 := by exact prefixLift 1294333
  have htrace : WordTrace (prefixWord ++ tailWord_1294333) baseStart_1294333 baseEnd_1294333 := by
    simpa [prefixWord, tailWord_1294333, baseEnd_1294333] using wordTrace_append hprefix tailTrace_1294333
  have hstable : (prefixWord ++ tailWord_1294333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294333).length < 2 ^ (prefixWord ++ tailWord_1294333).sum := by decide
  have hdescent : baseEnd_1294333 < baseStart_1294333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294334 : List Nat := [4, 2, 2, 2, 1, 2, 1, 4, 1, 2, 2]
def baseStart_1294334 : Nat := 118140960795 + 1294334 * 2 ^ 59
def prefixEnd_1294334 : Nat := 4983230072969 + 3 ^ 40 * 1294334 * 2
def baseEnd_1294334 : Nat := 664615469456644145972473

theorem tailTrace_1294334 : CollatzResearch.WordTrace tailWord_1294334 prefixEnd_1294334 664615469456644145972473 := by
  unfold tailWord_1294334
  simp only [CollatzResearch.WordTrace]
  refine ⟨5901029911607055936656257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31472159528570964995500037 5901029911607055936656257)
  ·
    refine ⟨4425772433705291952492193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5901029911607055936656257 4425772433705291952492193)
    ·
      refine ⟨3319329325278968964369145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4425772433705291952492193 3319329325278968964369145)
      ·
        refine ⟨2489496993959226723276859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3319329325278968964369145 2489496993959226723276859)
        ·
          refine ⟨3734245490938840084915289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2489496993959226723276859 3734245490938840084915289)
          ·
            refine ⟨2800684118204130063686467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3734245490938840084915289 2800684118204130063686467)
            ·
              refine ⟨4201026177306195095529701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2800684118204130063686467 4201026177306195095529701)
              ·
                refine ⟨787692408244911580411819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4201026177306195095529701 787692408244911580411819)
                ·
                  refine ⟨1181538612367367370617729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 787692408244911580411819 1181538612367367370617729)
                  ·
                    refine ⟨886153959275525527963297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1181538612367367370617729 886153959275525527963297)
                    ·
                      refine ⟨664615469456644145972473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 886153959275525527963297 664615469456644145972473)
                      ·
                        rfl

theorem cell23_1294334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_1294334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294334 prefixEnd_1294334 := by exact prefixLift 1294334
  have htrace : WordTrace (prefixWord ++ tailWord_1294334) baseStart_1294334 baseEnd_1294334 := by
    simpa [prefixWord, tailWord_1294334, baseEnd_1294334] using wordTrace_append hprefix tailTrace_1294334
  have hstable : (prefixWord ++ tailWord_1294334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294334).length < 2 ^ (prefixWord ++ tailWord_1294334).sum := by decide
  have hdescent : baseEnd_1294334 < baseStart_1294334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294340 : List Nat := [2, 3, 2, 4, 2, 1, 1, 8]
def baseStart_1294340 : Nat := 118140960795 + 1294340 * 2 ^ 59
def prefixEnd_1294340 : Nat := 4983230072969 + 3 ^ 40 * 1294340 * 2
def baseEnd_1294340 : Nat := 24615501864465597129535

theorem tailTrace_1294340 : CollatzResearch.WordTrace tailWord_1294340 prefixEnd_1294340 24615501864465597129535 := by
  unfold tailWord_1294340
  simp only [CollatzResearch.WordTrace]
  refine ⟨23604229065417355258984237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31472305420556473678645649 23604229065417355258984237)
  ·
    refine ⟨8851585899531508222119089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23604229065417355258984237 8851585899531508222119089)
    ·
      refine ⟨6638689424648631166589317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8851585899531508222119089 6638689424648631166589317)
      ·
        refine ⟨1244754267121618343735497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6638689424648631166589317 1244754267121618343735497)
        ·
          refine ⟨933565700341213757801623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1244754267121618343735497 933565700341213757801623)
          ·
            refine ⟨1400348550511820636702435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 933565700341213757801623 1400348550511820636702435)
            ·
              refine ⟨2100522825767730955053653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1400348550511820636702435 2100522825767730955053653)
              ·
                refine ⟨24615501864465597129535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2100522825767730955053653 24615501864465597129535)
                ·
                  rfl

theorem cell23_1294340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 8].length) (baseStart_1294340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294340 prefixEnd_1294340 := by exact prefixLift 1294340
  have htrace : WordTrace (prefixWord ++ tailWord_1294340) baseStart_1294340 baseEnd_1294340 := by
    simpa [prefixWord, tailWord_1294340, baseEnd_1294340] using wordTrace_append hprefix tailTrace_1294340
  have hstable : (prefixWord ++ tailWord_1294340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294340).length < 2 ^ (prefixWord ++ tailWord_1294340).sum := by decide
  have hdescent : baseEnd_1294340 < baseStart_1294340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294343 : List Nat := [1, 1, 4, 3, 1, 2, 1, 2, 3, 3, 2]
def baseStart_1294343 : Nat := 118140960795 + 1294343 * 2 ^ 59
def prefixEnd_1294343 : Nat := 4983230072969 + 3 ^ 40 * 1294343 * 2
def baseEnd_1294343 : Nat := 664620090782534610759931

theorem tailTrace_1294343 : CollatzResearch.WordTrace tailWord_1294343 prefixEnd_1294343 664620090782534610759931 := by
  unfold tailWord_1294343
  simp only [CollatzResearch.WordTrace]
  refine ⟨47208567549823842030327683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31472378366549228020218455 47208567549823842030327683)
  ·
    refine ⟨70812851324735763045491525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47208567549823842030327683 70812851324735763045491525)
    ·
      refine ⟨13277409623387955571029661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70812851324735763045491525 13277409623387955571029661)
      ·
        refine ⟨4979028608770483339136123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13277409623387955571029661 4979028608770483339136123)
        ·
          refine ⟨7468542913155725008704185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4979028608770483339136123 7468542913155725008704185)
          ·
            refine ⟨5601407184866793756528139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7468542913155725008704185 5601407184866793756528139)
            ·
              refine ⟨8402110777300190634792209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5601407184866793756528139 8402110777300190634792209)
              ·
                refine ⟨6301583082975142976094157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8402110777300190634792209 6301583082975142976094157)
                ·
                  refine ⟨2363093656115678616035309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6301583082975142976094157 2363093656115678616035309)
                  ·
                    refine ⟨886160121043379481013241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2363093656115678616035309 886160121043379481013241)
                    ·
                      refine ⟨664620090782534610759931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 886160121043379481013241 664620090782534610759931)
                      ·
                        rfl

theorem cell23_1294343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_1294343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294343 prefixEnd_1294343 := by exact prefixLift 1294343
  have htrace : WordTrace (prefixWord ++ tailWord_1294343) baseStart_1294343 baseEnd_1294343 := by
    simpa [prefixWord, tailWord_1294343, baseEnd_1294343] using wordTrace_append hprefix tailTrace_1294343
  have hstable : (prefixWord ++ tailWord_1294343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294343).length < 2 ^ (prefixWord ++ tailWord_1294343).sum := by decide
  have hdescent : baseEnd_1294343 < baseStart_1294343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294373 : List Nat := [1, 3, 1, 2, 2, 3, 2, 2, 1, 4, 2]
def baseStart_1294373 : Nat := 118140960795 + 1294373 * 2 ^ 59
def prefixEnd_1294373 : Nat := 4983230072969 + 3 ^ 40 * 1294373 * 2
def baseEnd_1294373 : Nat := 664635495202169493384793

theorem tailTrace_1294373 : CollatzResearch.WordTrace tailWord_1294373 prefixEnd_1294373 664635495202169493384793 := by
  unfold tailWord_1294373
  simp only [CollatzResearch.WordTrace]
  refine ⟨47209661739715157153919773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31473107826476771435946515 47209661739715157153919773)
  ·
    refine ⟨17703623152393183932719915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47209661739715157153919773 17703623152393183932719915)
    ·
      refine ⟨26555434728589775899079873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17703623152393183932719915 26555434728589775899079873)
      ·
        refine ⟨19916576046442331924309905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26555434728589775899079873 19916576046442331924309905)
        ·
          refine ⟨14937432034831748943232429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19916576046442331924309905 14937432034831748943232429)
          ·
            refine ⟨5601537013061905853712161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14937432034831748943232429 5601537013061905853712161)
            ·
              refine ⟨4201152759796429390284121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5601537013061905853712161 4201152759796429390284121)
              ·
                refine ⟨3150864569847322042713091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4201152759796429390284121 3150864569847322042713091)
                ·
                  refine ⟨4726296854770983064069637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3150864569847322042713091 4726296854770983064069637)
                  ·
                    refine ⟨886180660269559324513057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4726296854770983064069637 886180660269559324513057)
                    ·
                      refine ⟨664635495202169493384793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 886180660269559324513057 664635495202169493384793)
                      ·
                        rfl

theorem cell23_1294373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 4, 2].length) (baseStart_1294373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294373 prefixEnd_1294373 := by exact prefixLift 1294373
  have htrace : WordTrace (prefixWord ++ tailWord_1294373) baseStart_1294373 baseEnd_1294373 := by
    simpa [prefixWord, tailWord_1294373, baseEnd_1294373] using wordTrace_append hprefix tailTrace_1294373
  have hstable : (prefixWord ++ tailWord_1294373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294373).length < 2 ^ (prefixWord ++ tailWord_1294373).sum := by decide
  have hdescent : baseEnd_1294373 < baseStart_1294373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294386 : List Nat := [3, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4]
def baseStart_1294386 : Nat := 118140960795 + 1294386 * 2 ^ 59
def prefixEnd_1294386 : Nat := 4983230072969 + 3 ^ 40 * 1294386 * 2
def baseEnd_1294386 : Nat := 664642170450677942522233

theorem tailTrace_1294386 : CollatzResearch.WordTrace tailWord_1294386 prefixEnd_1294386 664642170450677942522233 := by
  unfold tailWord_1294386
  simp only [CollatzResearch.WordTrace]
  refine ⟨11802533972167015093535753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31473423925778706916095341 11802533972167015093535753)
  ·
    refine ⟨8851900479125261320151815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11802533972167015093535753 8851900479125261320151815)
    ·
      refine ⟨13277850718687891980227723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8851900479125261320151815 13277850718687891980227723)
      ·
        refine ⟨19916776078031837970341585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13277850718687891980227723 19916776078031837970341585)
        ·
          refine ⟨14937582058523878477756189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19916776078031837970341585 14937582058523878477756189)
          ·
            refine ⟨5601593271946454429158571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14937582058523878477756189 5601593271946454429158571)
            ·
              refine ⟨8402389907919681643737857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5601593271946454429158571 8402389907919681643737857)
              ·
                refine ⟨6301792430939761232803393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8402389907919681643737857 6301792430939761232803393)
                ·
                  refine ⟨4726344323204820924602545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6301792430939761232803393 4726344323204820924602545)
                  ·
                    refine ⟨3544758242403615693451909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4726344323204820924602545 3544758242403615693451909)
                    ·
                      refine ⟨664642170450677942522233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3544758242403615693451909 664642170450677942522233)
                      ·
                        rfl

theorem cell23_1294386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_1294386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294386 prefixEnd_1294386 := by exact prefixLift 1294386
  have htrace : WordTrace (prefixWord ++ tailWord_1294386) baseStart_1294386 baseEnd_1294386 := by
    simpa [prefixWord, tailWord_1294386, baseEnd_1294386] using wordTrace_append hprefix tailTrace_1294386
  have hstable : (prefixWord ++ tailWord_1294386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294386).length < 2 ^ (prefixWord ++ tailWord_1294386).sum := by decide
  have hdescent : baseEnd_1294386 < baseStart_1294386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294396 : List Nat := [2, 2, 2, 2, 2, 1, 4, 1, 7]
def baseStart_1294396 : Nat := 118140960795 + 1294396 * 2 ^ 59
def prefixEnd_1294396 : Nat := 4983230072969 + 3 ^ 40 * 1294396 * 2
def baseEnd_1294396 : Nat := 73849700584135878155243

theorem tailTrace_1294396 : CollatzResearch.WordTrace tailWord_1294396 prefixEnd_1294396 73849700584135878155243 := by
  unfold tailWord_1294396
  simp only [CollatzResearch.WordTrace]
  refine ⟨23605250309315916041003521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31473667079087888054671361 23605250309315916041003521)
  ·
    refine ⟨17703937731986937030752641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23605250309315916041003521 17703937731986937030752641)
    ·
      refine ⟨13277953298990202773064481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17703937731986937030752641 13277953298990202773064481)
      ·
        refine ⟨9958464974242652079798361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13277953298990202773064481 9958464974242652079798361)
        ·
          refine ⟨7468848730681989059848771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9958464974242652079798361 7468848730681989059848771)
          ·
            refine ⟨11203273096022983589773157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7468848730681989059848771 11203273096022983589773157)
            ·
              refine ⟨2100613705504309423082467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11203273096022983589773157 2100613705504309423082467)
              ·
                refine ⟨3150920558256464134623701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2100613705504309423082467 3150920558256464134623701)
                ·
                  refine ⟨73849700584135878155243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3150920558256464134623701 73849700584135878155243)
                  ·
                    rfl

theorem cell23_1294396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 7].length) (baseStart_1294396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294396 prefixEnd_1294396 := by exact prefixLift 1294396
  have htrace : WordTrace (prefixWord ++ tailWord_1294396) baseStart_1294396 baseEnd_1294396 := by
    simpa [prefixWord, tailWord_1294396, baseEnd_1294396] using wordTrace_append hprefix tailTrace_1294396
  have hstable : (prefixWord ++ tailWord_1294396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294396).length < 2 ^ (prefixWord ++ tailWord_1294396).sum := by decide
  have hdescent : baseEnd_1294396 < baseStart_1294396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294407 : List Nat := [1, 1, 4, 1, 3, 1, 5, 1, 2, 2, 2]
def baseStart_1294407 : Nat := 118140960795 + 1294407 * 2 ^ 59
def prefixEnd_1294407 : Nat := 4983230072969 + 3 ^ 40 * 1294407 * 2
def baseEnd_1294407 : Nat := 664652953544422360359637

theorem tailTrace_1294407 : CollatzResearch.WordTrace tailWord_1294407 prefixEnd_1294407 664652953544422360359637 := by
  unfold tailWord_1294407
  simp only [CollatzResearch.WordTrace]
  refine ⟨47210901821591980960657475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31473934547727987307104983 47210901821591980960657475)
  ·
    refine ⟨70816352732387971440986213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47210901821591980960657475 70816352732387971440986213)
    ·
      refine ⟨13278066137322744645184915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70816352732387971440986213 13278066137322744645184915)
      ·
        refine ⟨19917099205984116967777373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13278066137322744645184915 19917099205984116967777373)
        ·
          refine ⟨7468912202244043862916515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19917099205984116967777373 7468912202244043862916515)
          ·
            refine ⟨11203368303366065794374773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7468912202244043862916515 11203368303366065794374773)
            ·
              refine ⟨1050315778440568668222635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11203368303366065794374773 1050315778440568668222635)
              ·
                refine ⟨1575473667660853002333953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1050315778440568668222635 1575473667660853002333953)
                ·
                  refine ⟨1181605250745639751750465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1575473667660853002333953 1181605250745639751750465)
                  ·
                    refine ⟨886203938059229813812849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1181605250745639751750465 886203938059229813812849)
                    ·
                      refine ⟨664652953544422360359637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 886203938059229813812849 664652953544422360359637)
                      ·
                        rfl

theorem cell23_1294407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 2, 2, 2].length) (baseStart_1294407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294407 prefixEnd_1294407 := by exact prefixLift 1294407
  have htrace : WordTrace (prefixWord ++ tailWord_1294407) baseStart_1294407 baseEnd_1294407 := by
    simpa [prefixWord, tailWord_1294407, baseEnd_1294407] using wordTrace_append hprefix tailTrace_1294407
  have hstable : (prefixWord ++ tailWord_1294407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294407).length < 2 ^ (prefixWord ++ tailWord_1294407).sum := by decide
  have hdescent : baseEnd_1294407 < baseStart_1294407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294409 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 3, 7]
def baseStart_1294409 : Nat := 118140960795 + 1294409 * 2 ^ 59
def prefixEnd_1294409 : Nat := 4983230072969 + 3 ^ 40 * 1294409 * 2
def baseEnd_1294409 : Nat := 221551326835243784178209

theorem tailTrace_1294409 : CollatzResearch.WordTrace tailWord_1294409 prefixEnd_1294409 221551326835243784178209 := by
  unfold tailWord_1294409
  simp only [CollatzResearch.WordTrace]
  refine ⟨47210974767584735302230281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31473983178389823534820187 47210974767584735302230281)
  ·
    refine ⟨35408231075688551476672711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47210974767584735302230281 35408231075688551476672711)
    ·
      refine ⟨53112346613532827215009067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35408231075688551476672711 53112346613532827215009067)
      ·
        refine ⟨79668519920299240822513601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53112346613532827215009067 79668519920299240822513601)
        ·
          refine ⟨59751389940224430616885201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79668519920299240822513601 59751389940224430616885201)
          ·
            refine ⟨44813542455168322962663901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59751389940224430616885201 44813542455168322962663901)
            ·
              refine ⟨16805078420688121110998963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44813542455168322962663901 16805078420688121110998963)
              ·
                refine ⟨25207617631032181666498445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16805078420688121110998963 25207617631032181666498445)
                ·
                  refine ⟨9452856611637068124936917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25207617631032181666498445 9452856611637068124936917)
                  ·
                    refine ⟨221551326835243784178209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9452856611637068124936917 221551326835243784178209)
                    ·
                      rfl

theorem cell23_1294409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 7].length) (baseStart_1294409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294409 prefixEnd_1294409 := by exact prefixLift 1294409
  have htrace : WordTrace (prefixWord ++ tailWord_1294409) baseStart_1294409 baseEnd_1294409 := by
    simpa [prefixWord, tailWord_1294409, baseEnd_1294409] using wordTrace_append hprefix tailTrace_1294409
  have hstable : (prefixWord ++ tailWord_1294409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294409).length < 2 ^ (prefixWord ++ tailWord_1294409).sum := by decide
  have hdescent : baseEnd_1294409 < baseStart_1294409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294426 : List Nat := [3, 1, 1, 2, 1, 1, 4, 3, 2, 5]
def baseStart_1294426 : Nat := 118140960795 + 1294426 * 2 ^ 59
def prefixEnd_1294426 : Nat := 4983230072969 + 3 ^ 40 * 1294426 * 2
def baseEnd_1294426 : Nat := 221554236558952595340683

theorem tailTrace_1294426 : CollatzResearch.WordTrace tailWord_1294426 prefixEnd_1294426 221554236558952595340683 := by
  unfold tailWord_1294426
  simp only [CollatzResearch.WordTrace]
  refine ⟨11802898702130786801399783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31474396539015431470399421 11802898702130786801399783)
  ·
    refine ⟨17704348053196180202099675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11802898702130786801399783 17704348053196180202099675)
    ·
      refine ⟨26556522079794270303149513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17704348053196180202099675 26556522079794270303149513)
      ·
        refine ⟨19917391559845702727362135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26556522079794270303149513 19917391559845702727362135)
        ·
          refine ⟨29876087339768554091043203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19917391559845702727362135 29876087339768554091043203)
          ·
            refine ⟨44814131009652831136564805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29876087339768554091043203 44814131009652831136564805)
            ·
              refine ⟨8402649564309905838105901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44814131009652831136564805 8402649564309905838105901)
              ·
                refine ⟨3150993586616214689289713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8402649564309905838105901 3150993586616214689289713)
                ·
                  refine ⟨2363245189962161016967285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3150993586616214689289713 2363245189962161016967285)
                  ·
                    refine ⟨221554236558952595340683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2363245189962161016967285 221554236558952595340683)
                    ·
                      rfl

theorem cell23_1294426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 2, 5].length) (baseStart_1294426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294426 prefixEnd_1294426 := by exact prefixLift 1294426
  have htrace : WordTrace (prefixWord ++ tailWord_1294426) baseStart_1294426 baseEnd_1294426 := by
    simpa [prefixWord, tailWord_1294426, baseEnd_1294426] using wordTrace_append hprefix tailTrace_1294426
  have hstable : (prefixWord ++ tailWord_1294426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294426).length < 2 ^ (prefixWord ++ tailWord_1294426).sum := by decide
  have hdescent : baseEnd_1294426 < baseStart_1294426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294523 : List Nat := [1, 1, 1, 1, 1, 2, 6, 2, 1, 5, 2]
def baseStart_1294523 : Nat := 118140960795 + 1294523 * 2 ^ 59
def prefixEnd_1294523 : Nat := 4983230072969 + 3 ^ 40 * 1294523 * 2
def baseEnd_1294523 : Nat := 664712517300343906509103

theorem tailTrace_1294523 : CollatzResearch.WordTrace tailWord_1294523 prefixEnd_1294523 664712517300343906509103 := by
  unfold tailWord_1294523
  simp only [CollatzResearch.WordTrace]
  refine ⟨47215132689171732771880223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31476755126114488514586815 47215132689171732771880223)
  ·
    refine ⟨70822699033757599157820335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47215132689171732771880223 70822699033757599157820335)
    ·
      refine ⟨106234048550636398736730503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70822699033757599157820335 106234048550636398736730503)
      ·
        refine ⟨159351072825954598105095755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106234048550636398736730503 159351072825954598105095755)
        ·
          refine ⟨239026609238931897157643633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159351072825954598105095755 239026609238931897157643633)
          ·
            refine ⟨179269956929198922868232725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239026609238931897157643633 179269956929198922868232725)
            ·
              refine ⟨8403279231056199509448409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 179269956929198922868232725 8403279231056199509448409)
              ·
                refine ⟨6302459423292149632086307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8403279231056199509448409 6302459423292149632086307)
                ·
                  refine ⟨9453689134938224448129461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6302459423292149632086307 9453689134938224448129461)
                  ·
                    refine ⟨886283356400458542012137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9453689134938224448129461 886283356400458542012137)
                    ·
                      refine ⟨664712517300343906509103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 886283356400458542012137 664712517300343906509103)
                      ·
                        rfl

theorem cell23_1294523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 5, 2].length) (baseStart_1294523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294523 prefixEnd_1294523 := by exact prefixLift 1294523
  have htrace : WordTrace (prefixWord ++ tailWord_1294523) baseStart_1294523 baseEnd_1294523 := by
    simpa [prefixWord, tailWord_1294523, baseEnd_1294523] using wordTrace_append hprefix tailTrace_1294523
  have hstable : (prefixWord ++ tailWord_1294523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294523).length < 2 ^ (prefixWord ++ tailWord_1294523).sum := by decide
  have hdescent : baseEnd_1294523 < baseStart_1294523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294603 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 3, 3, 3]
def baseStart_1294603 : Nat := 118140960795 + 1294603 * 2 ^ 59
def prefixEnd_1294603 : Nat := 4983230072969 + 3 ^ 40 * 1294603 * 2
def baseEnd_1294603 : Nat := 664753595752703593508735

theorem tailTrace_1294603 : CollatzResearch.WordTrace tailWord_1294603 prefixEnd_1294603 664753595752703593508735 := by
  unfold tailWord_1294603
  simp only [CollatzResearch.WordTrace]
  refine ⟨47218050528881906434792463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31478700352587937623194975 47218050528881906434792463)
  ·
    refine ⟨70827075793322859652188695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47218050528881906434792463 70827075793322859652188695)
    ·
      refine ⟨106240613689984289478283043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70827075793322859652188695 106240613689984289478283043)
      ·
        refine ⟨159360920534976434217424565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106240613689984289478283043 159360920534976434217424565)
        ·
          refine ⟨14940086300154040707883553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 159360920534976434217424565 14940086300154040707883553)
          ·
            refine ⟨11205064725115530530912665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14940086300154040707883553 11205064725115530530912665)
            ·
              refine ⟨8403798543836647898184499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11205064725115530530912665 8403798543836647898184499)
              ·
                refine ⟨12605697815754971847276749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8403798543836647898184499 12605697815754971847276749)
                ·
                  refine ⟨4727136680908114442728781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12605697815754971847276749 4727136680908114442728781)
                  ·
                    refine ⟨1772676255340542916023293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4727136680908114442728781 1772676255340542916023293)
                    ·
                      refine ⟨664753595752703593508735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1772676255340542916023293 664753595752703593508735)
                      ·
                        rfl

theorem cell23_1294603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3, 3].length) (baseStart_1294603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294603 prefixEnd_1294603 := by exact prefixLift 1294603
  have htrace : WordTrace (prefixWord ++ tailWord_1294603) baseStart_1294603 baseEnd_1294603 := by
    simpa [prefixWord, tailWord_1294603, baseEnd_1294603] using wordTrace_append hprefix tailTrace_1294603
  have hstable : (prefixWord ++ tailWord_1294603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294603).length < 2 ^ (prefixWord ++ tailWord_1294603).sum := by decide
  have hdescent : baseEnd_1294603 < baseStart_1294603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294621 : List Nat := [1, 4, 2, 3, 2, 2, 1, 1, 3, 2, 2]
def baseStart_1294621 : Nat := 118140960795 + 1294621 * 2 ^ 59
def prefixEnd_1294621 : Nat := 4983230072969 + 3 ^ 40 * 1294621 * 2
def baseEnd_1294621 : Nat := 664762838404484523083653

theorem tailTrace_1294621 : CollatzResearch.WordTrace tailWord_1294621 prefixEnd_1294621 664762838404484523083653 := by
  unfold tailWord_1294621
  simp only [CollatzResearch.WordTrace]
  refine ⟨47218707042816695508947717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31479138028544463672631811 47218707042816695508947717)
  ·
    refine ⟨8853507570528130407927697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47218707042816695508947717 8853507570528130407927697)
    ·
      refine ⟨6640130677896097805945773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8853507570528130407927697 6640130677896097805945773)
      ·
        refine ⟨2490049004211036677229665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6640130677896097805945773 2490049004211036677229665)
        ·
          refine ⟨1867536753158277507922249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2490049004211036677229665 1867536753158277507922249)
          ·
            refine ⟨1400652564868708130941687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1867536753158277507922249 1400652564868708130941687)
            ·
              refine ⟨2100978847303062196412531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1400652564868708130941687 2100978847303062196412531)
              ·
                refine ⟨3151468270954593294618797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2100978847303062196412531 3151468270954593294618797)
                ·
                  refine ⟨1181800601607972485482049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3151468270954593294618797 1181800601607972485482049)
                  ·
                    refine ⟨886350451205979364111537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1181800601607972485482049 886350451205979364111537)
                    ·
                      refine ⟨664762838404484523083653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 886350451205979364111537 664762838404484523083653)
                      ·
                        rfl

theorem cell23_1294621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_1294621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294621 prefixEnd_1294621 := by exact prefixLift 1294621
  have htrace : WordTrace (prefixWord ++ tailWord_1294621) baseStart_1294621 baseEnd_1294621 := by
    simpa [prefixWord, tailWord_1294621, baseEnd_1294621] using wordTrace_append hprefix tailTrace_1294621
  have hstable : (prefixWord ++ tailWord_1294621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294621).length < 2 ^ (prefixWord ++ tailWord_1294621).sum := by decide
  have hdescent : baseEnd_1294621 < baseStart_1294621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294631 : List Nat := [1, 1, 8, 1, 1, 1, 1, 3, 2, 4]
def baseStart_1294631 : Nat := 118140960795 + 1294631 * 2 ^ 59
def prefixEnd_1294631 : Nat := 4983230072969 + 3 ^ 40 * 1294631 * 2
def baseEnd_1294631 : Nat := 221589324403676494652869

theorem tailTrace_1294631 : CollatzResearch.WordTrace tailWord_1294631 prefixEnd_1294631 221589324403676494652869 := by
  unfold tailWord_1294631
  simp only [CollatzResearch.WordTrace]
  refine ⟨47219071772780467216811747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31479381181853644811207831 47219071772780467216811747)
  ·
    refine ⟨70828607659170700825217621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47219071772780467216811747 70828607659170700825217621)
    ·
      refine ⟨830022746005906650295519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 70828607659170700825217621 830022746005906650295519)
      ·
        refine ⟨1245034119008859975443279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 830022746005906650295519 1245034119008859975443279)
        ·
          refine ⟨1867551178513289963164919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1245034119008859975443279 1867551178513289963164919)
          ·
            refine ⟨2801326767769934944747379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1867551178513289963164919 2801326767769934944747379)
            ·
              refine ⟨4201990151654902417121069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2801326767769934944747379 4201990151654902417121069)
              ·
                refine ⟨1575746306870588406420401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4201990151654902417121069 1575746306870588406420401)
                ·
                  refine ⟨1181809730152941304815301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1575746306870588406420401 1181809730152941304815301)
                  ·
                    refine ⟨221589324403676494652869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1181809730152941304815301 221589324403676494652869)
                    ·
                      rfl

theorem cell23_1294631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_1294631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294631 prefixEnd_1294631 := by exact prefixLift 1294631
  have htrace : WordTrace (prefixWord ++ tailWord_1294631) baseStart_1294631 baseEnd_1294631 := by
    simpa [prefixWord, tailWord_1294631, baseEnd_1294631] using wordTrace_append hprefix tailTrace_1294631
  have hstable : (prefixWord ++ tailWord_1294631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294631).length < 2 ^ (prefixWord ++ tailWord_1294631).sum := by decide
  have hdescent : baseEnd_1294631 < baseStart_1294631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294663 : List Nat := [1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 5]
def baseStart_1294663 : Nat := 118140960795 + 1294663 * 2 ^ 59
def prefixEnd_1294663 : Nat := 4983230072969 + 3 ^ 40 * 1294663 * 2
def baseEnd_1294663 : Nat := 664784404591973358758459

theorem tailTrace_1294663 : CollatzResearch.WordTrace tailWord_1294663 prefixEnd_1294663 664784404591973358758459 := by
  unfold tailWord_1294663
  simp only [CollatzResearch.WordTrace]
  refine ⟨47220238908664536681976643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31480159272443024454651095 47220238908664536681976643)
  ·
    refine ⟨70830358362996805022964965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47220238908664536681976643 70830358362996805022964965)
    ·
      refine ⟨13280692193061900941805931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70830358362996805022964965 13280692193061900941805931)
      ·
        refine ⟨19921038289592851412708897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13280692193061900941805931 19921038289592851412708897)
        ·
          refine ⟨14940778717194638559531673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19921038289592851412708897 14940778717194638559531673)
          ·
            refine ⟨11205584037895978919648755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14940778717194638559531673 11205584037895978919648755)
            ·
              refine ⟨16808376056843968379473133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11205584037895978919648755 16808376056843968379473133)
              ·
                refine ⟨6303141021316488142302425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16808376056843968379473133 6303141021316488142302425)
                ·
                  refine ⟨4727355765987366106726819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6303141021316488142302425 4727355765987366106726819)
                  ·
                    refine ⟨7091033648981049160090229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4727355765987366106726819 7091033648981049160090229)
                    ·
                      refine ⟨664784404591973358758459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7091033648981049160090229 664784404591973358758459)
                      ·
                        rfl

theorem cell23_1294663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_1294663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294663 prefixEnd_1294663 := by exact prefixLift 1294663
  have htrace : WordTrace (prefixWord ++ tailWord_1294663) baseStart_1294663 baseEnd_1294663 := by
    simpa [prefixWord, tailWord_1294663, baseEnd_1294663] using wordTrace_append hprefix tailTrace_1294663
  have hstable : (prefixWord ++ tailWord_1294663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294663).length < 2 ^ (prefixWord ++ tailWord_1294663).sum := by decide
  have hdescent : baseEnd_1294663 < baseStart_1294663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294690 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_1294690 : Nat := 118140960795 + 1294690 * 2 ^ 59
def prefixEnd_1294690 : Nat := 4983230072969 + 3 ^ 40 * 1294690 * 2
def baseEnd_1294690 : Nat := 664798268569644753120835

theorem tailTrace_1294690 : CollatzResearch.WordTrace tailWord_1294690 prefixEnd_1294690 664798268569644753120835 := by
  unfold tailWord_1294690
  simp only [CollatzResearch.WordTrace]
  refine ⟨11805305919891680073302381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31480815786377813528806349 11805305919891680073302381)
  ·
    refine ⟨4426989719959380027488393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11805305919891680073302381 4426989719959380027488393)
    ·
      refine ⟨3320242289969535020616295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4426989719959380027488393 3320242289969535020616295)
      ·
        refine ⟨4980363434954302530924443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3320242289969535020616295 4980363434954302530924443)
        ·
          refine ⟨7470545152431453796386665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4980363434954302530924443 7470545152431453796386665)
          ·
            refine ⟨5602908864323590347289999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7470545152431453796386665 5602908864323590347289999)
            ·
              refine ⟨8404363296485385520934999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5602908864323590347289999 8404363296485385520934999)
              ·
                refine ⟨12606544944728078281402499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8404363296485385520934999 12606544944728078281402499)
                ·
                  refine ⟨18909817417092117422103749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12606544944728078281402499 18909817417092117422103749)
                  ·
                    refine ⟨3545590765704772016644453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18909817417092117422103749 3545590765704772016644453)
                    ·
                      refine ⟨664798268569644753120835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3545590765704772016644453 664798268569644753120835)
                      ·
                        rfl

theorem cell23_1294690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_1294690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294690 prefixEnd_1294690 := by exact prefixLift 1294690
  have htrace : WordTrace (prefixWord ++ tailWord_1294690) baseStart_1294690 baseEnd_1294690 := by
    simpa [prefixWord, tailWord_1294690, baseEnd_1294690] using wordTrace_append hprefix tailTrace_1294690
  have hstable : (prefixWord ++ tailWord_1294690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294690).length < 2 ^ (prefixWord ++ tailWord_1294690).sum := by decide
  have hdescent : baseEnd_1294690 < baseStart_1294690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294700 : List Nat := [2, 2, 1, 1, 6, 1, 1, 2, 7]
def baseStart_1294700 : Nat := 118140960795 + 1294700 * 2 ^ 59
def prefixEnd_1294700 : Nat := 4983230072969 + 3 ^ 40 * 1294700 * 2
def baseEnd_1294700 : Nat := 73867044819576634888421

theorem tailTrace_1294700 : CollatzResearch.WordTrace tailWord_1294700 prefixEnd_1294700 73867044819576634888421 := by
  unfold tailWord_1294700
  simp only [CollatzResearch.WordTrace]
  refine ⟨23610794204765246000536777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31481058939686994667382369 23610794204765246000536777)
  ·
    refine ⟨17708095653573934500402583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23610794204765246000536777 17708095653573934500402583)
    ·
      refine ⟨26562143480360901750603875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17708095653573934500402583 26562143480360901750603875)
      ·
        refine ⟨39843215220541352625905813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26562143480360901750603875 39843215220541352625905813)
        ·
          refine ⟨1867650713462875904339335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39843215220541352625905813 1867650713462875904339335)
          ·
            refine ⟨2801476070194313856509003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1867650713462875904339335 2801476070194313856509003)
            ·
              refine ⟨4202214105291470784763505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2801476070194313856509003 4202214105291470784763505)
              ·
                refine ⟨3151660578968603088572629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4202214105291470784763505 3151660578968603088572629)
                ·
                  refine ⟨73867044819576634888421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3151660578968603088572629 73867044819576634888421)
                  ·
                    rfl

theorem cell23_1294700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 7].length) (baseStart_1294700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294700 prefixEnd_1294700 := by exact prefixLift 1294700
  have htrace : WordTrace (prefixWord ++ tailWord_1294700) baseStart_1294700 baseEnd_1294700 := by
    simpa [prefixWord, tailWord_1294700, baseEnd_1294700] using wordTrace_append hprefix tailTrace_1294700
  have hstable : (prefixWord ++ tailWord_1294700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294700).length < 2 ^ (prefixWord ++ tailWord_1294700).sum := by decide
  have hdescent : baseEnd_1294700 < baseStart_1294700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294717 : List Nat := [1, 4, 1, 1, 2, 4, 2, 3, 5]
def baseStart_1294717 : Nat := 118140960795 + 1294717 * 2 ^ 59
def prefixEnd_1294717 : Nat := 4983230072969 + 3 ^ 40 * 1294717 * 2
def baseEnd_1294717 : Nat := 73868014727479571942579

theorem tailTrace_1294717 : CollatzResearch.WordTrace tailWord_1294717 prefixEnd_1294717 73868014727479571942579 := by
  unfold tailWord_1294717
  simp only [CollatzResearch.WordTrace]
  refine ⟨47222208450468903904442405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31481472300312602602961603 47222208450468903904442405)
  ·
    refine ⟨8854164084462919482082951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47222208450468903904442405 8854164084462919482082951)
    ·
      refine ⟨13281246126694379223124427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8854164084462919482082951 13281246126694379223124427)
      ·
        refine ⟨19921869190041568834686641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13281246126694379223124427 19921869190041568834686641)
        ·
          refine ⟨14941401892531176626014981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19921869190041568834686641 14941401892531176626014981)
          ·
            refine ⟨2801512854849595617377809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14941401892531176626014981 2801512854849595617377809)
            ·
              refine ⟨2101134641137196713033357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2801512854849595617377809 2101134641137196713033357)
              ·
                refine ⟨787925490426448767387509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2101134641137196713033357 787925490426448767387509)
                ·
                  refine ⟨73868014727479571942579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 787925490426448767387509 73868014727479571942579)
                  ·
                    rfl

theorem cell23_1294717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3, 5].length) (baseStart_1294717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294717 prefixEnd_1294717 := by exact prefixLift 1294717
  have htrace : WordTrace (prefixWord ++ tailWord_1294717) baseStart_1294717 baseEnd_1294717 := by
    simpa [prefixWord, tailWord_1294717, baseEnd_1294717] using wordTrace_append hprefix tailTrace_1294717
  have hstable : (prefixWord ++ tailWord_1294717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294717).length < 2 ^ (prefixWord ++ tailWord_1294717).sum := by decide
  have hdescent : baseEnd_1294717 < baseStart_1294717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294770 : List Nat := [3, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3]
def baseStart_1294770 : Nat := 118140960795 + 1294770 * 2 ^ 59
def prefixEnd_1294770 : Nat := 4983230072969 + 3 ^ 40 * 1294770 * 2
def baseEnd_1294770 : Nat := 664839347022004440120467

theorem tailTrace_1294770 : CollatzResearch.WordTrace tailWord_1294770 prefixEnd_1294770 664839347022004440120467 := by
  unfold tailWord_1294770
  simp only [CollatzResearch.WordTrace]
  refine ⟨11806035379819223489030441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31482761012851262637414509 11806035379819223489030441)
  ·
    refine ⟨8854526534864417616772831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11806035379819223489030441 8854526534864417616772831)
    ·
      refine ⟨13281789802296626425159247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8854526534864417616772831 13281789802296626425159247)
      ·
        refine ⟨19922684703444939637738871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13281789802296626425159247 19922684703444939637738871)
        ·
          refine ⟨29884027055167409456608307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19922684703444939637738871 29884027055167409456608307)
          ·
            refine ⟨44826040582751114184912461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29884027055167409456608307 44826040582751114184912461)
            ·
              refine ⟨16809765218531667819342173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44826040582751114184912461 16809765218531667819342173)
              ·
                refine ⟨6303661956949375432253315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16809765218531667819342173 6303661956949375432253315)
                ·
                  refine ⟨9455492935424063148379973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6303661956949375432253315 9455492935424063148379973)
                  ·
                    refine ⟨1772904925392011840321245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9455492935424063148379973 1772904925392011840321245)
                    ·
                      refine ⟨664839347022004440120467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1772904925392011840321245 664839347022004440120467)
                      ·
                        rfl

theorem cell23_1294770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_1294770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294770 prefixEnd_1294770 := by exact prefixLift 1294770
  have htrace : WordTrace (prefixWord ++ tailWord_1294770) baseStart_1294770 baseEnd_1294770 := by
    simpa [prefixWord, tailWord_1294770, baseEnd_1294770] using wordTrace_append hprefix tailTrace_1294770
  have hstable : (prefixWord ++ tailWord_1294770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294770).length < 2 ^ (prefixWord ++ tailWord_1294770).sum := by decide
  have hdescent : baseEnd_1294770 < baseStart_1294770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294793 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 1, 1, 8]
def baseStart_1294793 : Nat := 118140960795 + 1294793 * 2 ^ 59
def prefixEnd_1294793 : Nat := 4983230072969 + 3 ^ 40 * 1294793 * 2
def baseEnd_1294793 : Nat := 664851157077057850132861

theorem tailTrace_1294793 : CollatzResearch.WordTrace tailWord_1294793 prefixEnd_1294793 664851157077057850132861 := by
  unfold tailWord_1294793
  simp only [CollatzResearch.WordTrace]
  refine ⟨47224980398193568884209033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31483320265462379256139355 47224980398193568884209033)
  ·
    refine ⟨35418735298645176663156775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47224980398193568884209033 35418735298645176663156775)
    ·
      refine ⟨53128102947967764994735163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35418735298645176663156775 53128102947967764994735163)
      ·
        refine ⟨79692154421951647492102745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53128102947967764994735163 79692154421951647492102745)
        ·
          refine ⟨59769115816463735619077059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79692154421951647492102745 59769115816463735619077059)
          ·
            refine ⟨89653673724695603428615589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59769115816463735619077059 89653673724695603428615589)
            ·
              refine ⟨16810063823380425642865423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89653673724695603428615589 16810063823380425642865423)
              ·
                refine ⟨25215095735070638464298135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16810063823380425642865423 25215095735070638464298135)
                ·
                  refine ⟨37822643602605957696447203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25215095735070638464298135 37822643602605957696447203)
                  ·
                    refine ⟨56733965403908936544670805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37822643602605957696447203 56733965403908936544670805)
                    ·
                      refine ⟨664851157077057850132861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 56733965403908936544670805 664851157077057850132861)
                      ·
                        rfl

theorem cell23_1294793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 1, 8].length) (baseStart_1294793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294793 prefixEnd_1294793 := by exact prefixLift 1294793
  have htrace : WordTrace (prefixWord ++ tailWord_1294793) baseStart_1294793 baseEnd_1294793 := by
    simpa [prefixWord, tailWord_1294793, baseEnd_1294793] using wordTrace_append hprefix tailTrace_1294793
  have hstable : (prefixWord ++ tailWord_1294793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294793).length < 2 ^ (prefixWord ++ tailWord_1294793).sum := by decide
  have hdescent : baseEnd_1294793 < baseStart_1294793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294817 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 5, 1, 3]
def baseStart_1294817 : Nat := 118140960795 + 1294817 * 2 ^ 59
def prefixEnd_1294817 : Nat := 4983230072969 + 3 ^ 40 * 1294817 * 2
def baseEnd_1294817 : Nat := 664863480612765756232751

theorem tailTrace_1294817 : CollatzResearch.WordTrace tailWord_1294817 prefixEnd_1294817 664863480612765756232751 := by
  unfold tailWord_1294817
  simp only [CollatzResearch.WordTrace]
  refine ⟨47225855750106620983082705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31483903833404413988721803 47225855750106620983082705)
  ·
    refine ⟨35419391812579965737312029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47225855750106620983082705 35419391812579965737312029)
    ·
      refine ⟨13282271929717487151492011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35419391812579965737312029 13282271929717487151492011)
      ·
        refine ⟨19923407894576230727238017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13282271929717487151492011 19923407894576230727238017)
        ·
          refine ⟨14942555920932173045428513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19923407894576230727238017 14942555920932173045428513)
          ·
            refine ⟨11206916940699129784071385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14942555920932173045428513 11206916940699129784071385)
            ·
              refine ⟨8405187705524347338053539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11206916940699129784071385 8405187705524347338053539)
              ·
                refine ⟨12607781558286521007080309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8405187705524347338053539 12607781558286521007080309)
                ·
                  refine ⟨1181979521089361344413779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12607781558286521007080309 1181979521089361344413779)
                  ·
                    refine ⟨1772969281634042016620669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1181979521089361344413779 1772969281634042016620669)
                    ·
                      refine ⟨664863480612765756232751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1772969281634042016620669 664863480612765756232751)
                      ·
                        rfl

theorem cell23_1294817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_1294817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294817 prefixEnd_1294817 := by exact prefixLift 1294817
  have htrace : WordTrace (prefixWord ++ tailWord_1294817) baseStart_1294817 baseEnd_1294817 := by
    simpa [prefixWord, tailWord_1294817, baseEnd_1294817] using wordTrace_append hprefix tailTrace_1294817
  have hstable : (prefixWord ++ tailWord_1294817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294817).length < 2 ^ (prefixWord ++ tailWord_1294817).sum := by decide
  have hdescent : baseEnd_1294817 < baseStart_1294817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294867 : List Nat := [1, 1, 1, 2, 1, 5, 1, 5, 2, 4]
def baseStart_1294867 : Nat := 118140960795 + 1294867 * 2 ^ 59
def prefixEnd_1294867 : Nat := 4983230072969 + 3 ^ 40 * 1294867 * 2
def baseEnd_1294867 : Nat := 221629718215163520202507

theorem tailTrace_1294867 : CollatzResearch.WordTrace tailWord_1294867 prefixEnd_1294867 221629718215163520202507 := by
  unfold tailWord_1294867
  simp only [CollatzResearch.WordTrace]
  refine ⟨47227679399925479522402855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31485119599950319681601903 47227679399925479522402855)
  ·
    refine ⟨70841519099888219283604283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47227679399925479522402855 70841519099888219283604283)
    ·
      refine ⟨106262278649832328925406425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70841519099888219283604283 106262278649832328925406425)
      ·
        refine ⟨79696708987374246694054819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106262278649832328925406425 79696708987374246694054819)
        ·
          refine ⟨119545063481061370041082229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79696708987374246694054819 119545063481061370041082229)
          ·
            refine ⟨11207349701349503441351459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 119545063481061370041082229 11207349701349503441351459)
            ·
              refine ⟨16811024552024255162027189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11207349701349503441351459 16811024552024255162027189)
              ·
                refine ⟨1576033551752273921440049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16811024552024255162027189 1576033551752273921440049)
                ·
                  refine ⟨1182025163814205441080037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1576033551752273921440049 1182025163814205441080037)
                  ·
                    refine ⟨221629718215163520202507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1182025163814205441080037 221629718215163520202507)
                    ·
                      rfl

theorem cell23_1294867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2, 4].length) (baseStart_1294867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294867 prefixEnd_1294867 := by exact prefixLift 1294867
  have htrace : WordTrace (prefixWord ++ tailWord_1294867) baseStart_1294867 baseEnd_1294867 := by
    simpa [prefixWord, tailWord_1294867, baseEnd_1294867] using wordTrace_append hprefix tailTrace_1294867
  have hstable : (prefixWord ++ tailWord_1294867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294867).length < 2 ^ (prefixWord ++ tailWord_1294867).sum := by decide
  have hdescent : baseEnd_1294867 < baseStart_1294867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294874 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2]
def baseStart_1294874 : Nat := 118140960795 + 1294874 * 2 ^ 59
def prefixEnd_1294874 : Nat := 4983230072969 + 3 ^ 40 * 1294874 * 2
def baseEnd_1294874 : Nat := 664892749010072033219989

theorem tailTrace_1294874 : CollatzResearch.WordTrace tailWord_1294874 prefixEnd_1294874 664892749010072033219989 := by
  unfold tailWord_1294874
  simp only [CollatzResearch.WordTrace]
  refine ⟨11806983677725029929476919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31485289807266746478605117 11806983677725029929476919)
  ·
    refine ⟨17710475516587544894215379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11806983677725029929476919 17710475516587544894215379)
    ·
      refine ⟨26565713274881317341323069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17710475516587544894215379 26565713274881317341323069)
      ·
        refine ⟨9962142478080494002996151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26565713274881317341323069 9962142478080494002996151)
        ·
          refine ⟨14943213717120741004494227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9962142478080494002996151 14943213717120741004494227)
          ·
            refine ⟨22414820575681111506741341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14943213717120741004494227 22414820575681111506741341)
            ·
              refine ⟨8405557715880416815028003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22414820575681111506741341 8405557715880416815028003)
              ·
                refine ⟨12608336573820625222542005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8405557715880416815028003 12608336573820625222542005)
                ·
                  refine ⟨1182031553795683614613313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12608336573820625222542005 1182031553795683614613313)
                  ·
                    refine ⟨886523665346762710959985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1182031553795683614613313 886523665346762710959985)
                    ·
                      refine ⟨664892749010072033219989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 886523665346762710959985 664892749010072033219989)
                      ·
                        rfl

theorem cell23_1294874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_1294874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294874 prefixEnd_1294874 := by exact prefixLift 1294874
  have htrace : WordTrace (prefixWord ++ tailWord_1294874) baseStart_1294874 baseEnd_1294874 := by
    simpa [prefixWord, tailWord_1294874, baseEnd_1294874] using wordTrace_append hprefix tailTrace_1294874
  have hstable : (prefixWord ++ tailWord_1294874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294874).length < 2 ^ (prefixWord ++ tailWord_1294874).sum := by decide
  have hdescent : baseEnd_1294874 < baseStart_1294874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294908 : List Nat := [2, 2, 2, 2, 3, 1, 2, 4, 1, 2, 2]
def baseStart_1294908 : Nat := 118140960795 + 1294908 * 2 ^ 59
def prefixEnd_1294908 : Nat := 4983230072969 + 3 ^ 40 * 1294908 * 2
def baseEnd_1294908 : Nat := 664910207352324900194833

theorem tailTrace_1294908 : CollatzResearch.WordTrace tailWord_1294908 prefixEnd_1294908 664910207352324900194833 := by
  unfold tailWord_1294908
  simp only [CollatzResearch.WordTrace]
  refine ⟨23614587396388471762322689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31486116528517962349763585 23614587396388471762322689)
  ·
    refine ⟨17710940547291353821742017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23614587396388471762322689 17710940547291353821742017)
    ·
      refine ⟨13283205410468515366306513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17710940547291353821742017 13283205410468515366306513)
      ·
        refine ⟨9962404057851386524729885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13283205410468515366306513 9962404057851386524729885)
        ·
          refine ⟨3735901521694269946773707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9962404057851386524729885 3735901521694269946773707)
          ·
            refine ⟨5603852282541404920160561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3735901521694269946773707 5603852282541404920160561)
            ·
              refine ⟨4202889211906053690120421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5603852282541404920160561 4202889211906053690120421)
              ·
                refine ⟨788041727232385066897579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4202889211906053690120421 788041727232385066897579)
                ·
                  refine ⟨1182062590848577600346369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 788041727232385066897579 1182062590848577600346369)
                  ·
                    refine ⟨886546943136433200259777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1182062590848577600346369 886546943136433200259777)
                    ·
                      refine ⟨664910207352324900194833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 886546943136433200259777 664910207352324900194833)
                      ·
                        rfl

theorem cell23_1294908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_1294908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294908 prefixEnd_1294908 := by exact prefixLift 1294908
  have htrace : WordTrace (prefixWord ++ tailWord_1294908) baseStart_1294908 baseEnd_1294908 := by
    simpa [prefixWord, tailWord_1294908, baseEnd_1294908] using wordTrace_append hprefix tailTrace_1294908
  have hstable : (prefixWord ++ tailWord_1294908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294908).length < 2 ^ (prefixWord ++ tailWord_1294908).sum := by decide
  have hdescent : baseEnd_1294908 < baseStart_1294908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294920 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 4, 2, 5]
def baseStart_1294920 : Nat := 118140960795 + 1294920 * 2 ^ 59
def prefixEnd_1294920 : Nat := 4983230072969 + 3 ^ 40 * 1294920 * 2
def baseEnd_1294920 : Nat := 664916369120178853244777

theorem tailTrace_1294920 : CollatzResearch.WordTrace tailWord_1294920 prefixEnd_1294920 664916369120178853244777 := by
  unfold tailWord_1294920
  simp only [CollatzResearch.WordTrace]
  refine ⟨23614806234366734787041107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31486408312488979716054809 23614806234366734787041107)
  ·
    refine ⟨35422209351550102180561661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23614806234366734787041107 35422209351550102180561661)
    ·
      refine ⟨13283328506831288317710623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35422209351550102180561661 13283328506831288317710623)
      ·
        refine ⟨19924992760246932476565935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13283328506831288317710623 19924992760246932476565935)
        ·
          refine ⟨29887489140370398714848903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19924992760246932476565935 29887489140370398714848903)
          ·
            refine ⟨44831233710555598072273355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29887489140370398714848903 44831233710555598072273355)
            ·
              refine ⟨67246850565833397108410033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44831233710555598072273355 67246850565833397108410033)
              ·
                refine ⟨50435137924375047831307525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67246850565833397108410033 50435137924375047831307525)
                ·
                  refine ⟨9456588360820321468370161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50435137924375047831307525 9456588360820321468370161)
                  ·
                    refine ⟨7092441270615241101277621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9456588360820321468370161 7092441270615241101277621)
                    ·
                      refine ⟨664916369120178853244777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7092441270615241101277621 664916369120178853244777)
                      ·
                        rfl

theorem cell23_1294920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_1294920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294920 prefixEnd_1294920 := by exact prefixLift 1294920
  have htrace : WordTrace (prefixWord ++ tailWord_1294920) baseStart_1294920 baseEnd_1294920 := by
    simpa [prefixWord, tailWord_1294920, baseEnd_1294920] using wordTrace_append hprefix tailTrace_1294920
  have hstable : (prefixWord ++ tailWord_1294920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294920).length < 2 ^ (prefixWord ++ tailWord_1294920).sum := by decide
  have hdescent : baseEnd_1294920 < baseStart_1294920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294977 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_1294977 : Nat := 118140960795 + 1294977 * 2 ^ 59
def prefixEnd_1294977 : Nat := 4983230072969 + 3 ^ 40 * 1294977 * 2
def baseEnd_1294977 : Nat := 664945637517485130232015

theorem tailTrace_1294977 : CollatzResearch.WordTrace tailWord_1294977 prefixEnd_1294977 664945637517485130232015 := by
  unfold tailWord_1294977
  simp only [CollatzResearch.WordTrace]
  refine ⟨47231691429526968308907185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31487794286351312205938123 47231691429526968308907185)
  ·
    refine ⟨35423768572145226231680389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47231691429526968308907185 35423768572145226231680389)
    ·
      refine ⟨6641956607277229918440073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35423768572145226231680389 6641956607277229918440073)
      ·
        refine ⟨4981467455457922438830055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6641956607277229918440073 4981467455457922438830055)
        ·
          refine ⟨7472201183186883658245083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4981467455457922438830055 7472201183186883658245083)
          ·
            refine ⟨11208301774780325487367625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7472201183186883658245083 11208301774780325487367625)
            ·
              refine ⟨8406226331085244115525719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11208301774780325487367625 8406226331085244115525719)
              ·
                refine ⟨12609339496627866173288579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8406226331085244115525719 12609339496627866173288579)
                ·
                  refine ⟨18914009244941799259932869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12609339496627866173288579 18914009244941799259932869)
                  ·
                    refine ⟨3546376733426587361237413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18914009244941799259932869 3546376733426587361237413)
                    ·
                      refine ⟨664945637517485130232015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3546376733426587361237413 664945637517485130232015)
                      ·
                        rfl

theorem cell23_1294977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_1294977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294977 prefixEnd_1294977 := by exact prefixLift 1294977
  have htrace : WordTrace (prefixWord ++ tailWord_1294977) baseStart_1294977 baseEnd_1294977 := by
    simpa [prefixWord, tailWord_1294977, baseEnd_1294977] using wordTrace_append hprefix tailTrace_1294977
  have hstable : (prefixWord ++ tailWord_1294977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294977).length < 2 ^ (prefixWord ++ tailWord_1294977).sum := by decide
  have hdescent : baseEnd_1294977 < baseStart_1294977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294997 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 6, 3, 3]
def baseStart_1294997 : Nat := 118140960795 + 1294997 * 2 ^ 59
def prefixEnd_1294997 : Nat := 4983230072969 + 3 ^ 40 * 1294997 * 2
def baseEnd_1294997 : Nat := 664955907130575051981923

theorem tailTrace_1294997 : CollatzResearch.WordTrace tailWord_1294997 prefixEnd_1294997 664955907130575051981923 := by
  unfold tailWord_1294997
  simp only [CollatzResearch.WordTrace]
  refine ⟨47232420889454511724635245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31488280592969674483090163 47232420889454511724635245)
  ·
    refine ⟨17712157833545441896738217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47232420889454511724635245 17712157833545441896738217)
    ·
      refine ⟨13284118375159081422553663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17712157833545441896738217 13284118375159081422553663)
      ·
        refine ⟨19926177562738622133830495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13284118375159081422553663 19926177562738622133830495)
        ·
          refine ⟨29889266344107933200745743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19926177562738622133830495 29889266344107933200745743)
          ·
            refine ⟨44833899516161899801118615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29889266344107933200745743 44833899516161899801118615)
            ·
              refine ⟨67250849274242849701677923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44833899516161899801118615 67250849274242849701677923)
              ·
                refine ⟨100876273911364274552516885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67250849274242849701677923 100876273911364274552516885)
                ·
                  refine ⟨4728575339595200369649229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 100876273911364274552516885 4728575339595200369649229)
                  ·
                    refine ⟨1773215752348200138618461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4728575339595200369649229 1773215752348200138618461)
                    ·
                      refine ⟨664955907130575051981923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1773215752348200138618461 664955907130575051981923)
                      ·
                        rfl

theorem cell23_1294997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_1294997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1294997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1294997 prefixEnd_1294997 := by exact prefixLift 1294997
  have htrace : WordTrace (prefixWord ++ tailWord_1294997) baseStart_1294997 baseEnd_1294997 := by
    simpa [prefixWord, tailWord_1294997, baseEnd_1294997] using wordTrace_append hprefix tailTrace_1294997
  have hstable : (prefixWord ++ tailWord_1294997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294997).length < 2 ^ (prefixWord ++ tailWord_1294997).sum := by decide
  have hdescent : baseEnd_1294997 < baseStart_1294997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295021 : List Nat := [1, 5, 2, 1, 1, 3, 1, 4, 5]
def baseStart_1295021 : Nat := 118140960795 + 1295021 * 2 ^ 59
def prefixEnd_1295021 : Nat := 4983230072969 + 3 ^ 40 * 1295021 * 2
def baseEnd_1295021 : Nat := 73885358962920328675757

theorem tailTrace_1295021 : CollatzResearch.WordTrace tailWord_1295021 prefixEnd_1295021 73885358962920328675757 := by
  unfold tailWord_1295021
  simp only [CollatzResearch.WordTrace]
  refine ⟨47233296241367563823508917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31488864160911709215672611 47233296241367563823508917)
  ·
    refine ⟨4428121522628209108453961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47233296241367563823508917 4428121522628209108453961)
    ·
      refine ⟨3321091141971156831340471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4428121522628209108453961 3321091141971156831340471)
      ·
        refine ⟨4981636712956735247010707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3321091141971156831340471 4981636712956735247010707)
        ·
          refine ⟨7472455069435102870516061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4981636712956735247010707 7472455069435102870516061)
          ·
            refine ⟨2802170651038163576443523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7472455069435102870516061 2802170651038163576443523)
            ·
              refine ⟨4203255976557245364665285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2802170651038163576443523 4203255976557245364665285)
              ·
                refine ⟨788110495604483505874741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4203255976557245364665285 788110495604483505874741)
                ·
                  refine ⟨73885358962920328675757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 788110495604483505874741 73885358962920328675757)
                  ·
                    rfl

theorem cell23_1295021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_1295021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295021 prefixEnd_1295021 := by exact prefixLift 1295021
  have htrace : WordTrace (prefixWord ++ tailWord_1295021) baseStart_1295021 baseEnd_1295021 := by
    simpa [prefixWord, tailWord_1295021, baseEnd_1295021] using wordTrace_append hprefix tailTrace_1295021
  have hstable : (prefixWord ++ tailWord_1295021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295021).length < 2 ^ (prefixWord ++ tailWord_1295021).sum := by decide
  have hdescent : baseEnd_1295021 < baseStart_1295021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295027 : List Nat := [1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 5]
def baseStart_1295027 : Nat := 118140960795 + 1295027 * 2 ^ 59
def prefixEnd_1295027 : Nat := 4983230072969 + 3 ^ 40 * 1295027 * 2
def baseEnd_1295027 : Nat := 664971311550209934606785

theorem tailTrace_1295027 : CollatzResearch.WordTrace tailWord_1295027 prefixEnd_1295027 664971311550209934606785 := by
  unfold tailWord_1295027
  simp only [CollatzResearch.WordTrace]
  refine ⟨47233515079345826848227335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31489010052897217898818223 47233515079345826848227335)
  ·
    refine ⟨70850272619018740272341003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47233515079345826848227335 70850272619018740272341003)
    ·
      refine ⟨106275408928528110408511505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70850272619018740272341003 106275408928528110408511505)
      ·
        refine ⟨79706556696396082806383629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106275408928528110408511505 79706556696396082806383629)
        ·
          refine ⟨29889958761148531052393861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79706556696396082806383629 29889958761148531052393861)
          ·
            refine ⟨5604367267715349572323849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29889958761148531052393861 5604367267715349572323849)
            ·
              refine ⟨4203275450786512179242887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5604367267715349572323849 4203275450786512179242887)
              ·
                refine ⟨6304913176179768268864331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4203275450786512179242887 6304913176179768268864331)
                ·
                  refine ⟨9457369764269652403296497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6304913176179768268864331 9457369764269652403296497)
                  ·
                    refine ⟨7093027323202239302472373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9457369764269652403296497 7093027323202239302472373)
                    ·
                      refine ⟨664971311550209934606785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7093027323202239302472373 664971311550209934606785)
                      ·
                        rfl

theorem cell23_1295027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 5].length) (baseStart_1295027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295027 prefixEnd_1295027 := by exact prefixLift 1295027
  have htrace : WordTrace (prefixWord ++ tailWord_1295027) baseStart_1295027 baseEnd_1295027 := by
    simpa [prefixWord, tailWord_1295027, baseEnd_1295027] using wordTrace_append hprefix tailTrace_1295027
  have hstable : (prefixWord ++ tailWord_1295027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295027).length < 2 ^ (prefixWord ++ tailWord_1295027).sum := by decide
  have hdescent : baseEnd_1295027 < baseStart_1295027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295054 : List Nat := [4, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4]
def baseStart_1295054 : Nat := 118140960795 + 1295054 * 2 ^ 59
def prefixEnd_1295054 : Nat := 4983230072969 + 3 ^ 40 * 1295054 * 2
def baseEnd_1295054 : Nat := 664985175527881328969161

theorem tailTrace_1295054 : CollatzResearch.WordTrace tailWord_1295054 prefixEnd_1295054 664985175527881328969161 := by
  unfold tailWord_1295054
  simp only [CollatzResearch.WordTrace]
  refine ⟨5904312481281001307432527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31489666566832006972973477 5904312481281001307432527)
  ·
    refine ⟨8856468721921501961148791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5904312481281001307432527 8856468721921501961148791)
    ·
      refine ⟨13284703082882252941723187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8856468721921501961148791 13284703082882252941723187)
      ·
        refine ⟨19927054624323379412584781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13284703082882252941723187 19927054624323379412584781)
        ·
          refine ⟨7472645484121267279719293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19927054624323379412584781 7472645484121267279719293)
          ·
            refine ⟨2802242056545475229894735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7472645484121267279719293 2802242056545475229894735)
            ·
              refine ⟨4203363084818212844842103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2802242056545475229894735 4203363084818212844842103)
              ·
                refine ⟨6305044627227319267263155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4203363084818212844842103 6305044627227319267263155)
                ·
                  refine ⟨9457566940840978900894733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6305044627227319267263155 9457566940840978900894733)
                  ·
                    refine ⟨3546587602815367087835525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9457566940840978900894733 3546587602815367087835525)
                    ·
                      refine ⟨664985175527881328969161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3546587602815367087835525 664985175527881328969161)
                      ·
                        rfl

theorem cell23_1295054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_1295054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295054 prefixEnd_1295054 := by exact prefixLift 1295054
  have htrace : WordTrace (prefixWord ++ tailWord_1295054) baseStart_1295054 baseEnd_1295054 := by
    simpa [prefixWord, tailWord_1295054, baseEnd_1295054] using wordTrace_append hprefix tailTrace_1295054
  have hstable : (prefixWord ++ tailWord_1295054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295054).length < 2 ^ (prefixWord ++ tailWord_1295054).sum := by decide
  have hdescent : baseEnd_1295054 < baseStart_1295054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295081 : List Nat := [1, 2, 1, 1, 1, 2, 6, 4, 1, 4]
def baseStart_1295081 : Nat := 118140960795 + 1295081 * 2 ^ 59
def prefixEnd_1295081 : Nat := 4983230072969 + 3 ^ 40 * 1295081 * 2
def baseEnd_1295081 : Nat := 221666346501850907777179

theorem tailTrace_1295081 : CollatzResearch.WordTrace tailWord_1295081 prefixEnd_1295081 221666346501850907777179 := by
  unfold tailWord_1295081
  simp only [CollatzResearch.WordTrace]
  refine ⟨47235484621150194070693097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31490323080766796047128731 47235484621150194070693097)
  ·
    refine ⟨35426613465862645553019823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47235484621150194070693097 35426613465862645553019823)
    ·
      refine ⟨53139920198793968329529735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35426613465862645553019823 53139920198793968329529735)
      ·
        refine ⟨79709880298190952494294603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53139920198793968329529735 79709880298190952494294603)
        ·
          refine ⟨119564820447286428741441905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79709880298190952494294603 119564820447286428741441905)
          ·
            refine ⟨89673615335464821556081429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119564820447286428741441905 89673615335464821556081429)
            ·
              refine ⟨4203450718849913510441317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 89673615335464821556081429 4203450718849913510441317)
              ·
                refine ⟨788147009784358783207747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4203450718849913510441317 788147009784358783207747)
                ·
                  refine ⟨1182220514676538174811621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 788147009784358783207747 1182220514676538174811621)
                  ·
                    refine ⟨221666346501850907777179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1182220514676538174811621 221666346501850907777179)
                    ·
                      rfl

theorem cell23_1295081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4, 1, 4].length) (baseStart_1295081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295081 prefixEnd_1295081 := by exact prefixLift 1295081
  have htrace : WordTrace (prefixWord ++ tailWord_1295081) baseStart_1295081 baseEnd_1295081 := by
    simpa [prefixWord, tailWord_1295081, baseEnd_1295081] using wordTrace_append hprefix tailTrace_1295081
  have hstable : (prefixWord ++ tailWord_1295081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295081).length < 2 ^ (prefixWord ++ tailWord_1295081).sum := by decide
  have hdescent : baseEnd_1295081 < baseStart_1295081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295138 : List Nat := [3, 3, 1, 1, 2, 2, 3, 1, 3, 1, 3]
def baseStart_1295138 : Nat := 118140960795 + 1295138 * 2 ^ 59
def prefixEnd_1295138 : Nat := 4983230072969 + 3 ^ 40 * 1295138 * 2
def baseEnd_1295138 : Nat := 665028307902859000318775

theorem tailTrace_1295138 : CollatzResearch.WordTrace tailWord_1295138 prefixEnd_1295138 665028307902859000318775 := by
  unfold tailWord_1295138
  simp only [CollatzResearch.WordTrace]
  refine ⟨11809390895485923201379517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31491709054629128537012045 11809390895485923201379517)
  ·
    refine ⟨4428521585807221200517319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11809390895485923201379517 4428521585807221200517319)
    ·
      refine ⟨6642782378710831800775979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4428521585807221200517319 6642782378710831800775979)
      ·
        refine ⟨9964173568066247701163969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6642782378710831800775979 9964173568066247701163969)
        ·
          refine ⟨7473130176049685775872977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9964173568066247701163969 7473130176049685775872977)
          ·
            refine ⟨5604847632037264331904733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7473130176049685775872977 5604847632037264331904733)
            ·
              refine ⟨2101817862013974124464275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5604847632037264331904733 2101817862013974124464275)
              ·
                refine ⟨3152726793020961186696413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2101817862013974124464275 3152726793020961186696413)
                ·
                  refine ⟨1182272547382860445011155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3152726793020961186696413 1182272547382860445011155)
                  ·
                    refine ⟨1773408821074290667516733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1182272547382860445011155 1773408821074290667516733)
                    ·
                      refine ⟨665028307902859000318775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1773408821074290667516733 665028307902859000318775)
                      ·
                        rfl

theorem cell23_1295138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_1295138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295138 prefixEnd_1295138 := by exact prefixLift 1295138
  have htrace : WordTrace (prefixWord ++ tailWord_1295138) baseStart_1295138 baseEnd_1295138 := by
    simpa [prefixWord, tailWord_1295138, baseEnd_1295138] using wordTrace_append hprefix tailTrace_1295138
  have hstable : (prefixWord ++ tailWord_1295138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295138).length < 2 ^ (prefixWord ++ tailWord_1295138).sum := by decide
  have hdescent : baseEnd_1295138 < baseStart_1295138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295154 : List Nat := [3, 2, 1, 1, 3, 1, 2, 3, 1, 6]
def baseStart_1295154 : Nat := 118140960795 + 1295154 * 2 ^ 59
def prefixEnd_1295154 : Nat := 4983230072969 + 3 ^ 40 * 1295154 * 2
def baseEnd_1295154 : Nat := 221678841197776979239567

theorem tailTrace_1295154 : CollatzResearch.WordTrace tailWord_1295154 prefixEnd_1295154 221678841197776979239567 := by
  unfold tailWord_1295154
  simp only [CollatzResearch.WordTrace]
  refine ⟨11809536787471431884525129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31492098099923818358733677 11809536787471431884525129)
  ·
    refine ⟨8857152590603573913393847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11809536787471431884525129 8857152590603573913393847)
    ·
      refine ⟨13285728885905360870090771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8857152590603573913393847 13285728885905360870090771)
      ·
        refine ⟨19928593328858041305136157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13285728885905360870090771 19928593328858041305136157)
        ·
          refine ⟨7473222498321765489426059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19928593328858041305136157 7473222498321765489426059)
          ·
            refine ⟨11209833747482648234139089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7473222498321765489426059 11209833747482648234139089)
            ·
              refine ⟨8407375310611986175604317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11209833747482648234139089 8407375310611986175604317)
              ·
                refine ⟨3152765741479494815851619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8407375310611986175604317 3152765741479494815851619)
                ·
                  refine ⟨4729148612219242223777429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3152765741479494815851619 4729148612219242223777429)
                  ·
                    refine ⟨221678841197776979239567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4729148612219242223777429 221678841197776979239567)
                    ·
                      rfl

theorem cell23_1295154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_1295154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295154 prefixEnd_1295154 := by exact prefixLift 1295154
  have htrace : WordTrace (prefixWord ++ tailWord_1295154) baseStart_1295154 baseEnd_1295154 := by
    simpa [prefixWord, tailWord_1295154, baseEnd_1295154] using wordTrace_append hprefix tailTrace_1295154
  have hstable : (prefixWord ++ tailWord_1295154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295154).length < 2 ^ (prefixWord ++ tailWord_1295154).sum := by decide
  have hdescent : baseEnd_1295154 < baseStart_1295154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295158 : List Nat := [5, 1, 2, 2, 2, 1, 1, 1, 3, 5]
def baseStart_1295158 : Nat := 118140960795 + 1295158 * 2 ^ 59
def prefixEnd_1295158 : Nat := 4983230072969 + 3 ^ 40 * 1295158 * 2
def baseEnd_1295158 : Nat := 221679525838649640689561

theorem tailTrace_1295158 : CollatzResearch.WordTrace tailWord_1295158 prefixEnd_1295158 221679525838649640689561 := by
  unfold tailWord_1295158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2952393315116952263827883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31492195361247490814164085 2952393315116952263827883)
  ·
    refine ⟨4428589972675428395741825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2952393315116952263827883 4428589972675428395741825)
    ·
      refine ⟨3321442479506571296806369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4428589972675428395741825 3321442479506571296806369)
      ·
        refine ⟨2491081859629928472604777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3321442479506571296806369 2491081859629928472604777)
        ·
          refine ⟨1868311394722446354453583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2491081859629928472604777 1868311394722446354453583)
          ·
            refine ⟨2802467092083669531680375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1868311394722446354453583 2802467092083669531680375)
            ·
              refine ⟨4203700638125504297520563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2802467092083669531680375 4203700638125504297520563)
              ·
                refine ⟨6305550957188256446280845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4203700638125504297520563 6305550957188256446280845)
                ·
                  refine ⟨2364581608945596167355317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6305550957188256446280845 2364581608945596167355317)
                  ·
                    refine ⟨221679525838649640689561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2364581608945596167355317 221679525838649640689561)
                    ·
                      rfl

theorem cell23_1295158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_1295158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295158 prefixEnd_1295158 := by exact prefixLift 1295158
  have htrace : WordTrace (prefixWord ++ tailWord_1295158) baseStart_1295158 baseEnd_1295158 := by
    simpa [prefixWord, tailWord_1295158, baseEnd_1295158] using wordTrace_append hprefix tailTrace_1295158
  have hstable : (prefixWord ++ tailWord_1295158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295158).length < 2 ^ (prefixWord ++ tailWord_1295158).sum := by decide
  have hdescent : baseEnd_1295158 < baseStart_1295158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295165 : List Nat := [1, 4, 1, 4, 2, 1, 2, 1, 2, 3, 2]
def baseStart_1295165 : Nat := 118140960795 + 1295165 * 2 ^ 59
def prefixEnd_1295165 : Nat := 4983230072969 + 3 ^ 40 * 1295165 * 2
def baseEnd_1295165 : Nat := 665042171880530394681151

theorem tailTrace_1295165 : CollatzResearch.WordTrace tailWord_1295165 prefixEnd_1295165 665042171880530394681151 := by
  unfold tailWord_1295165
  simp only [CollatzResearch.WordTrace]
  refine ⟨47238548352845876416750949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31492365568563917611167299 47238548352845876416750949)
  ·
    refine ⟨8857227816158601828140803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47238548352845876416750949 8857227816158601828140803)
    ·
      refine ⟨13285841724237902742211205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8857227816158601828140803 13285841724237902742211205)
      ·
        refine ⟨2491095323294606764164601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13285841724237902742211205 2491095323294606764164601)
        ·
          refine ⟨1868321492470955073123451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2491095323294606764164601 1868321492470955073123451)
          ·
            refine ⟨2802482238706432609685177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1868321492470955073123451 2802482238706432609685177)
            ·
              refine ⟨2101861679029824457263883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2802482238706432609685177 2101861679029824457263883)
              ·
                refine ⟨3152792518544736685895825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2101861679029824457263883 3152792518544736685895825)
                ·
                  refine ⟨2364594388908552514421869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3152792518544736685895825 2364594388908552514421869)
                  ·
                    refine ⟨886722895840707192908201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2364594388908552514421869 886722895840707192908201)
                    ·
                      refine ⟨665042171880530394681151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 886722895840707192908201 665042171880530394681151)
                      ·
                        rfl

theorem cell23_1295165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_1295165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295165 prefixEnd_1295165 := by exact prefixLift 1295165
  have htrace : WordTrace (prefixWord ++ tailWord_1295165) baseStart_1295165 baseEnd_1295165 := by
    simpa [prefixWord, tailWord_1295165, baseEnd_1295165] using wordTrace_append hprefix tailTrace_1295165
  have hstable : (prefixWord ++ tailWord_1295165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295165).length < 2 ^ (prefixWord ++ tailWord_1295165).sum := by decide
  have hdescent : baseEnd_1295165 < baseStart_1295165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295244 : List Nat := [2, 2, 1, 2, 1, 2, 3, 2, 2, 6]
def baseStart_1295244 : Nat := 118140960795 + 1295244 * 2 ^ 59
def prefixEnd_1295244 : Nat := 4983230072969 + 3 ^ 40 * 1295244 * 2
def baseEnd_1295244 : Nat := 221694245617411861864429

theorem tailTrace_1295244 : CollatzResearch.WordTrace tailWord_1295244 prefixEnd_1295244 221694245617411861864429 := by
  unfold tailWord_1295244
  simp only [CollatzResearch.WordTrace]
  refine ⟨23620714859779836454438393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31494286479706448605917857 23620714859779836454438393)
  ·
    refine ⟨17715536144834877340828795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23620714859779836454438393 17715536144834877340828795)
    ·
      refine ⟨26573304217252316011243193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17715536144834877340828795 26573304217252316011243193)
      ·
        refine ⟨19929978162939237008432395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26573304217252316011243193 19929978162939237008432395)
        ·
          refine ⟨29894967244408855512648593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19929978162939237008432395 29894967244408855512648593)
          ·
            refine ⟨22421225433306641634486445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29894967244408855512648593 22421225433306641634486445)
            ·
              refine ⟨8407959537489990612932417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22421225433306641634486445 8407959537489990612932417)
              ·
                refine ⟨6305969653117492959699313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8407959537489990612932417 6305969653117492959699313)
                ·
                  refine ⟨4729477239838119719774485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6305969653117492959699313 4729477239838119719774485)
                  ·
                    refine ⟨221694245617411861864429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4729477239838119719774485 221694245617411861864429)
                    ·
                      rfl

theorem cell23_1295244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 2, 6].length) (baseStart_1295244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295244 prefixEnd_1295244 := by exact prefixLift 1295244
  have htrace : WordTrace (prefixWord ++ tailWord_1295244) baseStart_1295244 baseEnd_1295244 := by
    simpa [prefixWord, tailWord_1295244, baseEnd_1295244] using wordTrace_append hprefix tailTrace_1295244
  have hstable : (prefixWord ++ tailWord_1295244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295244).length < 2 ^ (prefixWord ++ tailWord_1295244).sum := by decide
  have hdescent : baseEnd_1295244 < baseStart_1295244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295338 : List Nat := [3, 1, 3, 1, 2, 3, 2, 1, 2, 5]
def baseStart_1295338 : Nat := 118140960795 + 1295338 * 2 ^ 59
def prefixEnd_1295338 : Nat := 4983230072969 + 3 ^ 40 * 1295338 * 2
def baseEnd_1295338 : Nat := 221710334677919405939285

theorem tailTrace_1295338 : CollatzResearch.WordTrace tailWord_1295338 prefixEnd_1295338 221710334677919405939285 := by
  unfold tailWord_1295338
  simp only [CollatzResearch.WordTrace]
  refine ⟨11811214545304781740699667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31496572120812751308532445 11811214545304781740699667)
  ·
    refine ⟨17716821817957172611049501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11811214545304781740699667 17716821817957172611049501)
    ·
      refine ⟨6643808181733939729143563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17716821817957172611049501 6643808181733939729143563)
      ·
        refine ⟨9965712272600909593715345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6643808181733939729143563 9965712272600909593715345)
        ·
          refine ⟨7474284204450682195286509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9965712272600909593715345 7474284204450682195286509)
          ·
            refine ⟨2802856576669005823232441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7474284204450682195286509 2802856576669005823232441)
            ·
              refine ⟨2102142432501754367424331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2802856576669005823232441 2102142432501754367424331)
              ·
                refine ⟨3153213648752631551136497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2102142432501754367424331 3153213648752631551136497)
                ·
                  refine ⟨2364910236564473663352373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3153213648752631551136497 2364910236564473663352373)
                  ·
                    refine ⟨221710334677919405939285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2364910236564473663352373 221710334677919405939285)
                    ·
                      rfl

theorem cell23_1295338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_1295338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295338 prefixEnd_1295338 := by exact prefixLift 1295338
  have htrace : WordTrace (prefixWord ++ tailWord_1295338) baseStart_1295338 baseEnd_1295338 := by
    simpa [prefixWord, tailWord_1295338, baseEnd_1295338] using wordTrace_append hprefix tailTrace_1295338
  have hstable : (prefixWord ++ tailWord_1295338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295338).length < 2 ^ (prefixWord ++ tailWord_1295338).sum := by decide
  have hdescent : baseEnd_1295338 < baseStart_1295338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295392 : List Nat := [2, 1, 1, 7, 1, 2, 1, 1, 2, 1, 4]
def baseStart_1295392 : Nat := 118140960795 + 1295392 * 2 ^ 59
def prefixEnd_1295392 : Nat := 4983230072969 + 3 ^ 40 * 1295392 * 2
def baseEnd_1295392 : Nat := 665158731989101006542607

theorem tailTrace_1295392 : CollatzResearch.WordTrace tailWord_1295392 prefixEnd_1295392 665158731989101006542607 := by
  unfold tailWord_1295392
  simp only [CollatzResearch.WordTrace]
  refine ⟨23623413861511747092632215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31497885148682329456842953 23623413861511747092632215)
  ·
    refine ⟨35435120792267620638948323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23623413861511747092632215 35435120792267620638948323)
    ·
      refine ⟨53152681188401430958422485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35435120792267620638948323 53152681188401430958422485)
      ·
        refine ⟨1245765965353158538088027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 53152681188401430958422485 1245765965353158538088027)
        ·
          refine ⟨1868648948029737807132041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1245765965353158538088027 1868648948029737807132041)
          ·
            refine ⟨1401486711022303355349031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1868648948029737807132041 1401486711022303355349031)
            ·
              refine ⟨2102230066533455033023547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1401486711022303355349031 2102230066533455033023547)
              ·
                refine ⟨3153345099800182549535321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2102230066533455033023547 3153345099800182549535321)
                ·
                  refine ⟨2365008824850136912151491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3153345099800182549535321 2365008824850136912151491)
                  ·
                    refine ⟨3547513237275205368227237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2365008824850136912151491 3547513237275205368227237)
                    ·
                      refine ⟨665158731989101006542607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3547513237275205368227237 665158731989101006542607)
                      ·
                        rfl

theorem cell23_1295392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_1295392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295392 prefixEnd_1295392 := by exact prefixLift 1295392
  have htrace : WordTrace (prefixWord ++ tailWord_1295392) baseStart_1295392 baseEnd_1295392 := by
    simpa [prefixWord, tailWord_1295392, baseEnd_1295392] using wordTrace_append hprefix tailTrace_1295392
  have hstable : (prefixWord ++ tailWord_1295392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295392).length < 2 ^ (prefixWord ++ tailWord_1295392).sum := by decide
  have hdescent : baseEnd_1295392 < baseStart_1295392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295395 : List Nat := [1, 1, 1, 4, 3, 4, 1, 1, 2, 2, 3]
def baseStart_1295395 : Nat := 118140960795 + 1295395 * 2 ^ 59
def prefixEnd_1295395 : Nat := 4983230072969 + 3 ^ 40 * 1295395 * 2
def baseEnd_1295395 : Nat := 665160272431064494805093

theorem tailTrace_1295395 : CollatzResearch.WordTrace tailWord_1295395 prefixEnd_1295395 665160272431064494805093 := by
  unfold tailWord_1295395
  simp only [CollatzResearch.WordTrace]
  refine ⟨47246937142012625697623639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31497958094675083798415759 47246937142012625697623639)
  ·
    refine ⟨70870405713018938546435459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47246937142012625697623639 70870405713018938546435459)
    ·
      refine ⟨106305608569528407819653189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70870405713018938546435459 106305608569528407819653189)
      ·
        refine ⟨19932301606786576466184973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106305608569528407819653189 19932301606786576466184973)
        ·
          refine ⟨7474613102544966174819365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19932301606786576466184973 7474613102544966174819365)
          ·
            refine ⟨1401489956727181157778631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7474613102544966174819365 1401489956727181157778631)
            ·
              refine ⟨2102234935090771736667947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1401489956727181157778631 2102234935090771736667947)
              ·
                refine ⟨3153352402636157605001921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2102234935090771736667947 3153352402636157605001921)
                ·
                  refine ⟨2365014301977118203751441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3153352402636157605001921 2365014301977118203751441)
                  ·
                    refine ⟨1773760726482838652813581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2365014301977118203751441 1773760726482838652813581)
                    ·
                      refine ⟨665160272431064494805093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1773760726482838652813581 665160272431064494805093)
                      ·
                        rfl

theorem cell23_1295395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_1295395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295395 prefixEnd_1295395 := by exact prefixLift 1295395
  have htrace : WordTrace (prefixWord ++ tailWord_1295395) baseStart_1295395 baseEnd_1295395 := by
    simpa [prefixWord, tailWord_1295395, baseEnd_1295395] using wordTrace_append hprefix tailTrace_1295395
  have hstable : (prefixWord ++ tailWord_1295395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295395).length < 2 ^ (prefixWord ++ tailWord_1295395).sum := by decide
  have hdescent : baseEnd_1295395 < baseStart_1295395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295408 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 5, 1, 3]
def baseStart_1295408 : Nat := 118140960795 + 1295408 * 2 ^ 59
def prefixEnd_1295408 : Nat := 4983230072969 + 3 ^ 40 * 1295408 * 2
def baseEnd_1295408 : Nat := 665166947679572943942533

theorem tailTrace_1295408 : CollatzResearch.WordTrace tailWord_1295408 prefixEnd_1295408 665166947679572943942533 := by
  unfold tailWord_1295408
  simp only [CollatzResearch.WordTrace]
  refine ⟨23623705645482764458923439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31498274193977019278564585 23623705645482764458923439)
  ·
    refine ⟨35435558468224146688385159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23623705645482764458923439 35435558468224146688385159)
    ·
      refine ⟨53153337702336220032577739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35435558468224146688385159 53153337702336220032577739)
      ·
        refine ⟨79730006553504330048866609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53153337702336220032577739 79730006553504330048866609)
        ·
          refine ⟨59797504915128247536649957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79730006553504330048866609 59797504915128247536649957)
          ·
            refine ⟨11212032171586546413121867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59797504915128247536649957 11212032171586546413121867)
            ·
              refine ⟨16818048257379819619682801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11212032171586546413121867 16818048257379819619682801)
              ·
                refine ⟨12613536193034864714762101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16818048257379819619682801 12613536193034864714762101)
                ·
                  refine ⟨1182519018097018567008947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12613536193034864714762101 1182519018097018567008947)
                  ·
                    refine ⟨1773778527145527850513421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1182519018097018567008947 1773778527145527850513421)
                    ·
                      refine ⟨665166947679572943942533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1773778527145527850513421 665166947679572943942533)
                      ·
                        rfl

theorem cell23_1295408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 5, 1, 3].length) (baseStart_1295408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1295408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1295408 prefixEnd_1295408 := by exact prefixLift 1295408
  have htrace : WordTrace (prefixWord ++ tailWord_1295408) baseStart_1295408 baseEnd_1295408 := by
    simpa [prefixWord, tailWord_1295408, baseEnd_1295408] using wordTrace_append hprefix tailTrace_1295408
  have hstable : (prefixWord ++ tailWord_1295408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295408).length < 2 ^ (prefixWord ++ tailWord_1295408).sum := by decide
  have hdescent : baseEnd_1295408 < baseStart_1295408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
