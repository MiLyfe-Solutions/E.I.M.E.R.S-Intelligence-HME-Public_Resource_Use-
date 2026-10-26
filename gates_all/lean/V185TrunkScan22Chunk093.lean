import V185TrunkScan22Chunk092

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_833994 : List Nat := [3, 1, 2, 1, 2, 2, 4, 2, 2, 3]
def baseStart_833994 : Nat := 118140960795 + 833994 * 2 ^ 59
def prefixEnd_833994 : Nat := 4983230072969 + 3 ^ 40 * 833994 * 2
def baseEnd_833994 : Nat := 285493189977276818893025

theorem tailTrace_833994 : CollatzResearch.WordTrace tailWord_833994 prefixEnd_833994 285493189977276818893025 := by
  unfold tailWord_833994
  simp only [CollatzResearch.WordTrace]
  refine ⟨7604565035147411920123259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20278840093726431786995357 7604565035147411920123259)
  ·
    refine ⟨11406847552721117880184889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7604565035147411920123259 11406847552721117880184889)
    ·
      refine ⟨8555135664540838410138667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11406847552721117880184889 8555135664540838410138667)
      ·
        refine ⟨12832703496811257615208001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8555135664540838410138667 12832703496811257615208001)
        ·
          refine ⟨9624527622608443211406001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12832703496811257615208001 9624527622608443211406001)
          ·
            refine ⟨7218395716956332408554501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9624527622608443211406001 7218395716956332408554501)
            ·
              refine ⟨1353449196929312326603969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7218395716956332408554501 1353449196929312326603969)
              ·
                refine ⟨1015086897696984244952977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1353449196929312326603969 1015086897696984244952977)
                ·
                  refine ⟨761315173272738183714733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1015086897696984244952977 761315173272738183714733)
                  ·
                    refine ⟨285493189977276818893025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 761315173272738183714733 285493189977276818893025)
                    ·
                      rfl

theorem cell22_833994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_833994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833994 prefixEnd_833994 := by exact prefixLift 833994
  have htrace : WordTrace (prefixWord ++ tailWord_833994) baseStart_833994 baseEnd_833994 := by
    simpa [prefixWord, tailWord_833994, baseEnd_833994] using wordTrace_append hprefix tailTrace_833994
  have hstable : (prefixWord ++ tailWord_833994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833994).length < 2 ^ (prefixWord ++ tailWord_833994).sum := by decide
  have hdescent : baseEnd_833994 < baseStart_833994 := by decide
  rcases family_descends (prefixWord ++ tailWord_833994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834035 : List Nat := [1, 1, 1, 2, 2, 2, 4, 2, 7]
def baseStart_834035 : Nat := 118140960795 + 834035 * 2 ^ 59
def prefixEnd_834035 : Nat := 4983230072969 + 3 ^ 40 * 834035 * 2
def baseEnd_834035 : Nat := 95169075038388792872633

theorem tailTrace_834035 : CollatzResearch.WordTrace tailWord_834035 prefixEnd_834035 95169075038388792872633 := by
  unfold tailWord_834035
  simp only [CollatzResearch.WordTrace]
  refine ⟨30419755533441111682735559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20279837022294074455157039 30419755533441111682735559)
  ·
    refine ⟨45629633300161667524103339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30419755533441111682735559 45629633300161667524103339)
    ·
      refine ⟨68444449950242501286155009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45629633300161667524103339 68444449950242501286155009)
      ·
        refine ⟨51333337462681875964616257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68444449950242501286155009 51333337462681875964616257)
        ·
          refine ⟨38500003097011406973462193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51333337462681875964616257 38500003097011406973462193)
          ·
            refine ⟨28875002322758555230096645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38500003097011406973462193 28875002322758555230096645)
            ·
              refine ⟨5414062935517229105643121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28875002322758555230096645 5414062935517229105643121)
              ·
                refine ⟨4060547201637921829232341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5414062935517229105643121 4060547201637921829232341)
                ·
                  refine ⟨95169075038388792872633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4060547201637921829232341 95169075038388792872633)
                  ·
                    rfl

theorem cell22_834035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 7].length) (baseStart_834035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834035 prefixEnd_834035 := by exact prefixLift 834035
  have htrace : WordTrace (prefixWord ++ tailWord_834035) baseStart_834035 baseEnd_834035 := by
    simpa [prefixWord, tailWord_834035, baseEnd_834035] using wordTrace_append hprefix tailTrace_834035
  have hstable : (prefixWord ++ tailWord_834035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834035).length < 2 ^ (prefixWord ++ tailWord_834035).sum := by decide
  have hdescent : baseEnd_834035 < baseStart_834035 := by decide
  rcases family_descends (prefixWord ++ tailWord_834035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834065 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 2, 8]
def baseStart_834065 : Nat := 118140960795 + 834065 * 2 ^ 59
def prefixEnd_834065 : Nat := 4983230072969 + 3 ^ 40 * 834065 * 2
def baseEnd_834065 : Nat := 285517494728256300367807

theorem tailTrace_834065 : CollatzResearch.WordTrace tailWord_834065 prefixEnd_834065 285517494728256300367807 := by
  unfold tailWord_834065
  simp only [CollatzResearch.WordTrace]
  refine ⟨30420849723332426806327649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20280566482221617870885099 30420849723332426806327649)
  ·
    refine ⟨22815637292499320104745737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30420849723332426806327649 22815637292499320104745737)
    ·
      refine ⟨17111727969374490078559303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22815637292499320104745737 17111727969374490078559303)
      ·
        refine ⟨25667591954061735117838955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17111727969374490078559303 25667591954061735117838955)
        ·
          refine ⟨38501387931092602676758433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25667591954061735117838955 38501387931092602676758433)
          ·
            refine ⟨28876040948319452007568825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38501387931092602676758433 28876040948319452007568825)
            ·
              refine ⟨21657030711239589005676619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28876040948319452007568825 21657030711239589005676619)
              ·
                refine ⟨32485546066859383508514929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21657030711239589005676619 32485546066859383508514929)
                ·
                  refine ⟨24364159550144537631386197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32485546066859383508514929 24364159550144537631386197)
                  ·
                    refine ⟨285517494728256300367807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24364159550144537631386197 285517494728256300367807)
                    ·
                      rfl

theorem cell22_834065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_834065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834065 prefixEnd_834065 := by exact prefixLift 834065
  have htrace : WordTrace (prefixWord ++ tailWord_834065) baseStart_834065 baseEnd_834065 := by
    simpa [prefixWord, tailWord_834065, baseEnd_834065] using wordTrace_append hprefix tailTrace_834065
  have hstable : (prefixWord ++ tailWord_834065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834065).length < 2 ^ (prefixWord ++ tailWord_834065).sum := by decide
  have hdescent : baseEnd_834065 < baseStart_834065 := by decide
  rcases family_descends (prefixWord ++ tailWord_834065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834069 : List Nat := [1, 3, 2, 1, 3, 1, 5, 1, 5]
def baseStart_834069 : Nat := 118140960795 + 834069 * 2 ^ 59
def prefixEnd_834069 : Nat := 4983230072969 + 3 ^ 40 * 834069 * 2
def baseEnd_834069 : Nat := 95172954670000541089265

theorem tailTrace_834069 : CollatzResearch.WordTrace tailWord_834069 prefixEnd_834069 95172954670000541089265 := by
  unfold tailWord_834069
  simp only [CollatzResearch.WordTrace]
  refine ⟨30420995615317935489473261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20280663743545290326315507 30420995615317935489473261)
  ·
    refine ⟨11407873355744225808552473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30420995615317935489473261 11407873355744225808552473)
    ·
      refine ⟨8555905016808169356414355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11407873355744225808552473 8555905016808169356414355)
      ·
        refine ⟨12833857525212254034621533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8555905016808169356414355 12833857525212254034621533)
        ·
          refine ⟨4812696571954595262983075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12833857525212254034621533 4812696571954595262983075)
          ·
            refine ⟨7219044857931892894474613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4812696571954595262983075 7219044857931892894474613)
            ·
              refine ⟨676785455431114958856995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7219044857931892894474613 676785455431114958856995)
              ·
                refine ⟨1015178183146672438285493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 676785455431114958856995 1015178183146672438285493)
                ·
                  refine ⟨95172954670000541089265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1015178183146672438285493 95172954670000541089265)
                  ·
                    rfl

theorem cell22_834069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 5].length) (baseStart_834069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834069 prefixEnd_834069 := by exact prefixLift 834069
  have htrace : WordTrace (prefixWord ++ tailWord_834069) baseStart_834069 baseEnd_834069 := by
    simpa [prefixWord, tailWord_834069, baseEnd_834069] using wordTrace_append hprefix tailTrace_834069
  have hstable : (prefixWord ++ tailWord_834069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834069).length < 2 ^ (prefixWord ++ tailWord_834069).sum := by decide
  have hdescent : baseEnd_834069 < baseStart_834069 := by decide
  rcases family_descends (prefixWord ++ tailWord_834069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834165 : List Nat := [1, 3, 4, 2, 2, 2, 2, 2, 4]
def baseStart_834165 : Nat := 118140960795 + 834165 * 2 ^ 59
def prefixEnd_834165 : Nat := 4983230072969 + 3 ^ 40 * 834165 * 2
def baseEnd_834165 : Nat := 95183908923963124289167

theorem tailTrace_834165 : CollatzResearch.WordTrace tailWord_834165 prefixEnd_834165 95183908923963124289167 := by
  unfold tailWord_834165
  simp only [CollatzResearch.WordTrace]
  refine ⟨30424497022970143884967949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20282998015313429256645299 30424497022970143884967949)
  ·
    refine ⟨11409186383613803956862981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30424497022970143884967949 11409186383613803956862981)
    ·
      refine ⟨2139222446927588241911809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11409186383613803956862981 2139222446927588241911809)
      ·
        refine ⟨1604416835195691181433857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2139222446927588241911809 1604416835195691181433857)
        ·
          refine ⟨1203312626396768386075393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1604416835195691181433857 1203312626396768386075393)
          ·
            refine ⟨902484469797576289556545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1203312626396768386075393 902484469797576289556545)
            ·
              refine ⟨676863352348182217167409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 902484469797576289556545 676863352348182217167409)
              ·
                refine ⟨507647514261136662875557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 676863352348182217167409 507647514261136662875557)
                ·
                  refine ⟨95183908923963124289167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 507647514261136662875557 95183908923963124289167)
                  ·
                    rfl

theorem cell22_834165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2, 4].length) (baseStart_834165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834165 prefixEnd_834165 := by exact prefixLift 834165
  have htrace : WordTrace (prefixWord ++ tailWord_834165) baseStart_834165 baseEnd_834165 := by
    simpa [prefixWord, tailWord_834165, baseEnd_834165] using wordTrace_append hprefix tailTrace_834165
  have hstable : (prefixWord ++ tailWord_834165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834165).length < 2 ^ (prefixWord ++ tailWord_834165).sum := by decide
  have hdescent : baseEnd_834165 < baseStart_834165 := by decide
  rcases family_descends (prefixWord ++ tailWord_834165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834172 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 2, 6]
def baseStart_834172 : Nat := 118140960795 + 834172 * 2 ^ 59
def prefixEnd_834172 : Nat := 4983230072969 + 3 ^ 40 * 834172 * 2
def baseEnd_834172 : Nat := 285554123014943687942479

theorem tailTrace_834172 : CollatzResearch.WordTrace tailWord_834172 prefixEnd_834172 285554123014943687942479 := by
  unfold tailWord_834172
  simp only [CollatzResearch.WordTrace]
  refine ⟨15212376166972392040236385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20283168222629856053648513 15212376166972392040236385)
  ·
    refine ⟨11409282125229294030177289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15212376166972392040236385 11409282125229294030177289)
    ·
      refine ⟨8556961593921970522632967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11409282125229294030177289 8556961593921970522632967)
      ·
        refine ⟨12835442390882955783949451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8556961593921970522632967 12835442390882955783949451)
        ·
          refine ⟨19253163586324433675924177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12835442390882955783949451 19253163586324433675924177)
          ·
            refine ⟨14439872689743325256943133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19253163586324433675924177 14439872689743325256943133)
            ·
              refine ⟨5414952258653746971353675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14439872689743325256943133 5414952258653746971353675)
              ·
                refine ⟨8122428387980620457030513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5414952258653746971353675 8122428387980620457030513)
                ·
                  refine ⟨6091821290985465342772885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8122428387980620457030513 6091821290985465342772885)
                  ·
                    refine ⟨285554123014943687942479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6091821290985465342772885 285554123014943687942479)
                    ·
                      rfl

theorem cell22_834172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_834172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834172 prefixEnd_834172 := by exact prefixLift 834172
  have htrace : WordTrace (prefixWord ++ tailWord_834172) baseStart_834172 baseEnd_834172 := by
    simpa [prefixWord, tailWord_834172, baseEnd_834172] using wordTrace_append hprefix tailTrace_834172
  have hstable : (prefixWord ++ tailWord_834172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834172).length < 2 ^ (prefixWord ++ tailWord_834172).sum := by decide
  have hdescent : baseEnd_834172 < baseStart_834172 := by decide
  rcases family_descends (prefixWord ++ tailWord_834172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834221 : List Nat := [1, 5, 2, 1, 1, 2, 3, 2, 5]
def baseStart_834221 : Nat := 118140960795 + 834221 * 2 ^ 59
def prefixEnd_834221 : Nat := 4983230072969 + 3 ^ 40 * 834221 * 2
def baseEnd_834221 : Nat := 95190298905441297822443

theorem tailTrace_834221 : CollatzResearch.WordTrace tailWord_834221 prefixEnd_834221 95190298905441297822443 := by
  unfold tailWord_834221
  simp only [CollatzResearch.WordTrace]
  refine ⟨30426539510767265449006517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20284359673844843632671011 30426539510767265449006517)
  ·
    refine ⟨2852488079134431135844361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30426539510767265449006517 2852488079134431135844361)
    ·
      refine ⟨2139366059350823351883271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2852488079134431135844361 2139366059350823351883271)
      ·
        refine ⟨3209049089026235027824907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2139366059350823351883271 3209049089026235027824907)
        ·
          refine ⟨4813573633539352541737361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3209049089026235027824907 4813573633539352541737361)
          ·
            refine ⟨3610180225154514406303021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4813573633539352541737361 3610180225154514406303021)
            ·
              refine ⟨1353817584432942902363633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3610180225154514406303021 1353817584432942902363633)
              ·
                refine ⟨1015363188324707176772725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1353817584432942902363633 1015363188324707176772725)
                ·
                  refine ⟨95190298905441297822443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1015363188324707176772725 95190298905441297822443)
                  ·
                    rfl

theorem cell22_834221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_834221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834221 prefixEnd_834221 := by exact prefixLift 834221
  have htrace : WordTrace (prefixWord ++ tailWord_834221) baseStart_834221 baseEnd_834221 := by
    simpa [prefixWord, tailWord_834221, baseEnd_834221] using wordTrace_append hprefix tailTrace_834221
  have hstable : (prefixWord ++ tailWord_834221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834221).length < 2 ^ (prefixWord ++ tailWord_834221).sum := by decide
  have hdescent : baseEnd_834221 < baseStart_834221 := by decide
  rcases family_descends (prefixWord ++ tailWord_834221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834268 : List Nat := [2, 2, 5, 1, 1, 1, 2, 3, 1, 4]
def baseStart_834268 : Nat := 118140960795 + 834268 * 2 ^ 59
def prefixEnd_834268 : Nat := 4983230072969 + 3 ^ 40 * 834268 * 2
def baseEnd_834268 : Nat := 285586985776831437542185

theorem tailTrace_834268 : CollatzResearch.WordTrace tailWord_834268 prefixEnd_834268 285586985776831437542185 := by
  unfold tailWord_834268
  simp only [CollatzResearch.WordTrace]
  refine ⟨15214126870798496237983729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20285502494397994983978305 15214126870798496237983729)
  ·
    refine ⟨11410595153098872178487797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15214126870798496237983729 11410595153098872178487797)
    ·
      refine ⟨1069743295603019266733231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11410595153098872178487797 1069743295603019266733231)
      ·
        refine ⟨1604614943404528900099847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1069743295603019266733231 1604614943404528900099847)
        ·
          refine ⟨2406922415106793350149771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1604614943404528900099847 2406922415106793350149771)
          ·
            refine ⟨3610383622660190025224657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2406922415106793350149771 3610383622660190025224657)
            ·
              refine ⟨2707787716995142518918493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3610383622660190025224657 2707787716995142518918493)
              ·
                refine ⟨1015420393873178444594435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2707787716995142518918493 1015420393873178444594435)
                ·
                  refine ⟨1523130590809767666891653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1015420393873178444594435 1523130590809767666891653)
                  ·
                    refine ⟨285586985776831437542185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1523130590809767666891653 285586985776831437542185)
                    ·
                      rfl

theorem cell22_834268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_834268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834268 prefixEnd_834268 := by exact prefixLift 834268
  have htrace : WordTrace (prefixWord ++ tailWord_834268) baseStart_834268 baseEnd_834268 := by
    simpa [prefixWord, tailWord_834268, baseEnd_834268] using wordTrace_append hprefix tailTrace_834268
  have hstable : (prefixWord ++ tailWord_834268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834268).length < 2 ^ (prefixWord ++ tailWord_834268).sum := by decide
  have hdescent : baseEnd_834268 < baseStart_834268 := by decide
  rcases family_descends (prefixWord ++ tailWord_834268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834298 : List Nat := [3, 1, 1, 1, 1, 3, 6, 1, 2, 3]
def baseStart_834298 : Nat := 118140960795 + 834298 * 2 ^ 59
def prefixEnd_834298 : Nat := 4983230072969 + 3 ^ 40 * 834298 * 2
def baseEnd_834298 : Nat := 285597255389921359292093

theorem tailTrace_834298 : CollatzResearch.WordTrace tailWord_834298 prefixEnd_834298 285597255389921359292093 := by
  unfold tailWord_834298
  simp only [CollatzResearch.WordTrace]
  refine ⟨7607336982872076899889887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20286231954325538399706365 7607336982872076899889887)
  ·
    refine ⟨11411005474308115349834831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7607336982872076899889887 11411005474308115349834831)
    ·
      refine ⟨17116508211462173024752247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11411005474308115349834831 17116508211462173024752247)
      ·
        refine ⟨25674762317193259537128371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17116508211462173024752247 25674762317193259537128371)
        ·
          refine ⟨38512143475789889305692557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25674762317193259537128371 38512143475789889305692557)
          ·
            refine ⟨14442053803421208489634709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38512143475789889305692557 14442053803421208489634709)
            ·
              refine ⟨676971272035369147951627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14442053803421208489634709 676971272035369147951627)
              ·
                refine ⟨1015456908053053721927441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 676971272035369147951627 1015456908053053721927441)
                ·
                  refine ⟨761592681039790291445581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1015456908053053721927441 761592681039790291445581)
                  ·
                    refine ⟨285597255389921359292093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 761592681039790291445581 285597255389921359292093)
                    ·
                      rfl

theorem cell22_834298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 2, 3].length) (baseStart_834298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834298 prefixEnd_834298 := by exact prefixLift 834298
  have htrace : WordTrace (prefixWord ++ tailWord_834298) baseStart_834298 baseEnd_834298 := by
    simpa [prefixWord, tailWord_834298, baseEnd_834298] using wordTrace_append hprefix tailTrace_834298
  have hstable : (prefixWord ++ tailWord_834298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834298).length < 2 ^ (prefixWord ++ tailWord_834298).sum := by decide
  have hdescent : baseEnd_834298 < baseStart_834298 := by decide
  rcases family_descends (prefixWord ++ tailWord_834298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834416 : List Nat := [2, 1, 1, 1, 4, 1, 5, 1, 1, 5]
def baseStart_834416 : Nat := 118140960795 + 834416 * 2 ^ 59
def prefixEnd_834416 : Nat := 4983230072969 + 3 ^ 40 * 834416 * 2
def baseEnd_834416 : Nat := 285637649201408384841731

theorem tailTrace_834416 : CollatzResearch.WordTrace tailWord_834416 prefixEnd_834416 285637649201408384841731 := by
  unfold tailWord_834416
  simp only [CollatzResearch.WordTrace]
  refine ⟨15216825872530406876177551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20289101163373875834903401 15216825872530406876177551)
  ·
    refine ⟨22825238808795610314266327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15216825872530406876177551 22825238808795610314266327)
    ·
      refine ⟨34237858213193415471399491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22825238808795610314266327 34237858213193415471399491)
      ·
        refine ⟨51356787319790123207099237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34237858213193415471399491 51356787319790123207099237)
        ·
          refine ⟨9629397622460648101331107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51356787319790123207099237 9629397622460648101331107)
          ·
            refine ⟨14444096433690972151996661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9629397622460648101331107 14444096433690972151996661)
            ·
              refine ⟨1354134040658528639249687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14444096433690972151996661 1354134040658528639249687)
              ·
                refine ⟨2031201060987792958874531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1354134040658528639249687 2031201060987792958874531)
                ·
                  refine ⟨3046801591481689438311797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2031201060987792958874531 3046801591481689438311797)
                  ·
                    refine ⟨285637649201408384841731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3046801591481689438311797 285637649201408384841731)
                    ·
                      rfl

theorem cell22_834416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 1, 5].length) (baseStart_834416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834416 prefixEnd_834416 := by exact prefixLift 834416
  have htrace : WordTrace (prefixWord ++ tailWord_834416) baseStart_834416 baseEnd_834416 := by
    simpa [prefixWord, tailWord_834416, baseEnd_834416] using wordTrace_append hprefix tailTrace_834416
  have hstable : (prefixWord ++ tailWord_834416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834416).length < 2 ^ (prefixWord ++ tailWord_834416).sum := by decide
  have hdescent : baseEnd_834416 < baseStart_834416 := by decide
  rcases family_descends (prefixWord ++ tailWord_834416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834506 : List Nat := [3, 1, 2, 1, 2, 1, 1, 4, 2, 5]
def baseStart_834506 : Nat := 118140960795 + 834506 * 2 ^ 59
def prefixEnd_834506 : Nat := 4983230072969 + 3 ^ 40 * 834506 * 2
def baseEnd_834506 : Nat := 285668458040678150091455

theorem tailTrace_834506 : CollatzResearch.WordTrace tailWord_834506 prefixEnd_834506 285668458040678150091455 := by
  unfold tailWord_834506
  simp only [CollatzResearch.WordTrace]
  refine ⟨7609233578683689780782843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20291289543156506082087581 7609233578683689780782843)
  ·
    refine ⟨11413850368025534671174265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7609233578683689780782843 11413850368025534671174265)
    ·
      refine ⟨8560387776019151003380699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11413850368025534671174265 8560387776019151003380699)
      ·
        refine ⟨12840581664028726505071049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8560387776019151003380699 12840581664028726505071049)
        ·
          refine ⟨9630436248021544878803287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12840581664028726505071049 9630436248021544878803287)
          ·
            refine ⟨14445654372032317318204931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9630436248021544878803287 14445654372032317318204931)
            ·
              refine ⟨21668481558048475977307397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14445654372032317318204931 21668481558048475977307397)
              ·
                refine ⟨4062840292134089245745137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21668481558048475977307397 4062840292134089245745137)
                ·
                  refine ⟨3047130219100566934308853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4062840292134089245745137 3047130219100566934308853)
                  ·
                    refine ⟨285668458040678150091455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3047130219100566934308853 285668458040678150091455)
                    ·
                      rfl

theorem cell22_834506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_834506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834506 prefixEnd_834506 := by exact prefixLift 834506
  have htrace : WordTrace (prefixWord ++ tailWord_834506) baseStart_834506 baseEnd_834506 := by
    simpa [prefixWord, tailWord_834506, baseEnd_834506] using wordTrace_append hprefix tailTrace_834506
  have hstable : (prefixWord ++ tailWord_834506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834506).length < 2 ^ (prefixWord ++ tailWord_834506).sum := by decide
  have hdescent : baseEnd_834506 < baseStart_834506 := by decide
  rcases family_descends (prefixWord ++ tailWord_834506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834508 : List Nat := [2, 2, 1, 4, 1, 1, 4, 2, 5]
def baseStart_834508 : Nat := 118140960795 + 834508 * 2 ^ 59
def prefixEnd_834508 : Nat := 4983230072969 + 3 ^ 40 * 834508 * 2
def baseEnd_834508 : Nat := 95223047560516937180483

theorem tailTrace_834508 : CollatzResearch.WordTrace tailWord_834508 prefixEnd_834508 95223047560516937180483 := by
  unfold tailWord_834508
  simp only [CollatzResearch.WordTrace]
  refine ⟨15218503630363756732352089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20291338173818342309802785 15218503630363756732352089)
  ·
    refine ⟨11413877722772817549264067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15218503630363756732352089 11413877722772817549264067)
    ·
      refine ⟨17120816584159226323896101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11413877722772817549264067 17120816584159226323896101)
      ·
        refine ⟨3210153109529854935730519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17120816584159226323896101 3210153109529854935730519)
        ·
          refine ⟨4815229664294782403595779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3210153109529854935730519 4815229664294782403595779)
          ·
            refine ⟨7222844496442173605393669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4815229664294782403595779 7222844496442173605393669)
            ·
              refine ⟨1354283343082907551011313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7222844496442173605393669 1354283343082907551011313)
              ·
                refine ⟨1015712507312180663258485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1354283343082907551011313 1015712507312180663258485)
                ·
                  refine ⟨95223047560516937180483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1015712507312180663258485 95223047560516937180483)
                  ·
                    rfl

theorem cell22_834508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 5].length) (baseStart_834508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834508 prefixEnd_834508 := by exact prefixLift 834508
  have htrace : WordTrace (prefixWord ++ tailWord_834508) baseStart_834508 baseEnd_834508 := by
    simpa [prefixWord, tailWord_834508, baseEnd_834508] using wordTrace_append hprefix tailTrace_834508
  have hstable : (prefixWord ++ tailWord_834508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834508).length < 2 ^ (prefixWord ++ tailWord_834508).sum := by decide
  have hdescent : baseEnd_834508 < baseStart_834508 := by decide
  rcases family_descends (prefixWord ++ tailWord_834508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834536 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 8]
def baseStart_834536 : Nat := 118140960795 + 834536 * 2 ^ 59
def prefixEnd_834536 : Nat := 4983230072969 + 3 ^ 40 * 834536 * 2
def baseEnd_834536 : Nat := 95226242551256023947121

theorem tailTrace_834536 : CollatzResearch.WordTrace tailWord_834536 prefixEnd_834536 95226242551256023947121 := by
  unfold tailWord_834536
  simp only [CollatzResearch.WordTrace]
  refine ⟨15219014252313037123361731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20292019003084049497815641 15219014252313037123361731)
  ·
    refine ⟨22828521378469555685042597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15219014252313037123361731 22828521378469555685042597)
    ·
      refine ⟨4280347758463041690945487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22828521378469555685042597 4280347758463041690945487)
      ·
        refine ⟨6420521637694562536418231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4280347758463041690945487 6420521637694562536418231)
        ·
          refine ⟨9630782456541843804627347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6420521637694562536418231 9630782456541843804627347)
          ·
            refine ⟨14446173684812765706941021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9630782456541843804627347 14446173684812765706941021)
            ·
              refine ⟨5417315131804787140102883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14446173684812765706941021 5417315131804787140102883)
              ·
                refine ⟨8125972697707180710154325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5417315131804787140102883 8125972697707180710154325)
                ·
                  refine ⟨95226242551256023947121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8125972697707180710154325 95226242551256023947121)
                  ·
                    rfl

theorem cell22_834536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 8].length) (baseStart_834536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834536 prefixEnd_834536 := by exact prefixLift 834536
  have htrace : WordTrace (prefixWord ++ tailWord_834536) baseStart_834536 baseEnd_834536 := by
    simpa [prefixWord, tailWord_834536, baseEnd_834536] using wordTrace_append hprefix tailTrace_834536
  have hstable : (prefixWord ++ tailWord_834536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834536).length < 2 ^ (prefixWord ++ tailWord_834536).sum := by decide
  have hdescent : baseEnd_834536 < baseStart_834536 := by decide
  rcases family_descends (prefixWord ++ tailWord_834536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834538 : List Nat := [3, 1, 3, 1, 2, 2, 2, 1, 3, 4]
def baseStart_834538 : Nat := 118140960795 + 834538 * 2 ^ 59
def prefixEnd_834538 : Nat := 4983230072969 + 3 ^ 40 * 834538 * 2
def baseEnd_834538 : Nat := 285679412294640733291357

theorem tailTrace_834538 : CollatzResearch.WordTrace tailWord_834538 prefixEnd_834538 285679412294640733291357 := by
  unfold tailWord_834538
  simp only [CollatzResearch.WordTrace]
  refine ⟨7609525362654707147074067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20292067633745885725530845 7609525362654707147074067)
  ·
    refine ⟨11414288043982060720611101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7609525362654707147074067 11414288043982060720611101)
    ·
      refine ⟨4280358016493272770229163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11414288043982060720611101 4280358016493272770229163)
      ·
        refine ⟨6420537024739909155343745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4280358016493272770229163 6420537024739909155343745)
        ·
          refine ⟨4815402768554931866507809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6420537024739909155343745 4815402768554931866507809)
          ·
            refine ⟨3611552076416198899880857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4815402768554931866507809 3611552076416198899880857)
            ·
              refine ⟨2708664057312149174910643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3611552076416198899880857 2708664057312149174910643)
              ·
                refine ⟨4062996085968223762365965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2708664057312149174910643 4062996085968223762365965)
                ·
                  refine ⟨1523623532238083910887237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4062996085968223762365965 1523623532238083910887237)
                  ·
                    refine ⟨285679412294640733291357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1523623532238083910887237 285679412294640733291357)
                    ·
                      rfl

theorem cell22_834538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_834538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834538 prefixEnd_834538 := by exact prefixLift 834538
  have htrace : WordTrace (prefixWord ++ tailWord_834538) baseStart_834538 baseEnd_834538 := by
    simpa [prefixWord, tailWord_834538, baseEnd_834538] using wordTrace_append hprefix tailTrace_834538
  have hstable : (prefixWord ++ tailWord_834538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834538).length < 2 ^ (prefixWord ++ tailWord_834538).sum := by decide
  have hdescent : baseEnd_834538 < baseStart_834538 := by decide
  rcases family_descends (prefixWord ++ tailWord_834538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834570 : List Nat := [3, 1, 2, 2, 3, 1, 2, 4, 4]
def baseStart_834570 : Nat := 118140960795 + 834570 * 2 ^ 59
def prefixEnd_834570 : Nat := 4983230072969 + 3 ^ 40 * 834570 * 2
def baseEnd_834570 : Nat := 95230122182867772163753

theorem tailTrace_834570 : CollatzResearch.WordTrace tailWord_834570 prefixEnd_834570 95230122182867772163753 := by
  unfold tailWord_834570
  simp only [CollatzResearch.WordTrace]
  refine ⟨7609817146625724513365291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20292845724335265368974109 7609817146625724513365291)
  ·
    refine ⟨11414725719938586770047937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7609817146625724513365291 11414725719938586770047937)
    ·
      refine ⟨8561044289953940077535953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11414725719938586770047937 8561044289953940077535953)
      ·
        refine ⟨6420783217465455058151965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8561044289953940077535953 6420783217465455058151965)
        ·
          refine ⟨2407793706549545646806987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6420783217465455058151965 2407793706549545646806987)
          ·
            refine ⟨3611690559824318470210481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2407793706549545646806987 3611690559824318470210481)
            ·
              refine ⟨2708767919868238852657861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3611690559824318470210481 2708767919868238852657861)
              ·
                refine ⟨507893984975294784873349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2708767919868238852657861 507893984975294784873349)
                ·
                  refine ⟨95230122182867772163753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 507893984975294784873349 95230122182867772163753)
                  ·
                    rfl

theorem cell22_834570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4, 4].length) (baseStart_834570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834570 prefixEnd_834570 := by exact prefixLift 834570
  have htrace : WordTrace (prefixWord ++ tailWord_834570) baseStart_834570 baseEnd_834570 := by
    simpa [prefixWord, tailWord_834570, baseEnd_834570] using wordTrace_append hprefix tailTrace_834570
  have hstable : (prefixWord ++ tailWord_834570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834570).length < 2 ^ (prefixWord ++ tailWord_834570).sum := by decide
  have hdescent : baseEnd_834570 < baseStart_834570 := by decide
  rcases family_descends (prefixWord ++ tailWord_834570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834583 : List Nat := [1, 1, 3, 5, 1, 1, 1, 2, 1, 6]
def baseStart_834583 : Nat := 118140960795 + 834583 * 2 ^ 59
def prefixEnd_834583 : Nat := 4983230072969 + 3 ^ 40 * 834583 * 2
def baseEnd_834583 : Nat := 285694816714275615916219

theorem tailTrace_834583 : CollatzResearch.WordTrace tailWord_834583 prefixEnd_834583 285694816714275615916219 := by
  unfold tailWord_834583
  simp only [CollatzResearch.WordTrace]
  refine ⟨30439742735455801273684403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20293161823637200849122935 30439742735455801273684403)
  ·
    refine ⟨45659614103183701910526605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30439742735455801273684403 45659614103183701910526605)
    ·
      refine ⟨17122355288693888216447477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45659614103183701910526605 17122355288693888216447477)
      ·
        refine ⟨1605220808315052020291951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17122355288693888216447477 1605220808315052020291951)
        ·
          refine ⟨2407831212472578030437927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1605220808315052020291951 2407831212472578030437927)
          ·
            refine ⟨3611746818708867045656891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2407831212472578030437927 3611746818708867045656891)
            ·
              refine ⟨5417620228063300568485337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3611746818708867045656891 5417620228063300568485337)
              ·
                refine ⟨4063215171047475426364003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5417620228063300568485337 4063215171047475426364003)
                ·
                  refine ⟨6094822756571213139546005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4063215171047475426364003 6094822756571213139546005)
                  ·
                    refine ⟨285694816714275615916219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6094822756571213139546005 285694816714275615916219)
                    ·
                      rfl

theorem cell22_834583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_834583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834583 prefixEnd_834583 := by exact prefixLift 834583
  have htrace : WordTrace (prefixWord ++ tailWord_834583) baseStart_834583 baseEnd_834583 := by
    simpa [prefixWord, tailWord_834583, baseEnd_834583] using wordTrace_append hprefix tailTrace_834583
  have hstable : (prefixWord ++ tailWord_834583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834583).length < 2 ^ (prefixWord ++ tailWord_834583).sum := by decide
  have hdescent : baseEnd_834583 < baseStart_834583 := by decide
  rcases family_descends (prefixWord ++ tailWord_834583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834611 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 1, 8]
def baseStart_834611 : Nat := 118140960795 + 834611 * 2 ^ 59
def prefixEnd_834611 : Nat := 4983230072969 + 3 ^ 40 * 834611 * 2
def baseEnd_834611 : Nat := 285704401686492876216133

theorem tailTrace_834611 : CollatzResearch.WordTrace tailWord_834611 prefixEnd_834611 285704401686492876216133 := by
  unfold tailWord_834611
  simp only [CollatzResearch.WordTrace]
  refine ⟨30440763979354362055703687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20293842652902908037135791 30440763979354362055703687)
  ·
    refine ⟨45661145969031543083555531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30440763979354362055703687 45661145969031543083555531)
    ·
      refine ⟨68491718953547314625333297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45661145969031543083555531 68491718953547314625333297)
      ·
        refine ⟨51368789215160485968999973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68491718953547314625333297 51368789215160485968999973)
        ·
          refine ⟨9631647977842591119187495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51368789215160485968999973 9631647977842591119187495)
          ·
            refine ⟨14447471966763886678781243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9631647977842591119187495 14447471966763886678781243)
            ·
              refine ⟨21671207950145830018171865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14447471966763886678781243 21671207950145830018171865)
              ·
                refine ⟨16253405962609372513628899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21671207950145830018171865 16253405962609372513628899)
                ·
                  refine ⟨24380108943914058770443349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16253405962609372513628899 24380108943914058770443349)
                  ·
                    refine ⟨285704401686492876216133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24380108943914058770443349 285704401686492876216133)
                    ·
                      rfl

theorem cell22_834611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 8].length) (baseStart_834611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834611 prefixEnd_834611 := by exact prefixLift 834611
  have htrace : WordTrace (prefixWord ++ tailWord_834611) baseStart_834611 baseEnd_834611 := by
    simpa [prefixWord, tailWord_834611, baseEnd_834611] using wordTrace_append hprefix tailTrace_834611
  have hstable : (prefixWord ++ tailWord_834611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834611).length < 2 ^ (prefixWord ++ tailWord_834611).sum := by decide
  have hdescent : baseEnd_834611 < baseStart_834611 := by decide
  rcases family_descends (prefixWord ++ tailWord_834611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834681 : List Nat := [1, 2, 1, 3, 5, 2, 2, 2, 1, 3]
def baseStart_834681 : Nat := 118140960795 + 834681 * 2 ^ 59
def prefixEnd_834681 : Nat := 4983230072969 + 3 ^ 40 * 834681 * 2
def baseEnd_834681 : Nat := 285728364117036026965919

theorem tailTrace_834681 : CollatzResearch.WordTrace tailWord_834681 prefixEnd_834681 285728364117036026965919 := by
  unfold tailWord_834681
  simp only [CollatzResearch.WordTrace]
  refine ⟨30443317089100764010751897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20295544726067176007167931 30443317089100764010751897)
  ·
    refine ⟨22832487816825573008063923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30443317089100764010751897 22832487816825573008063923)
    ·
      refine ⟨34248731725238359512095885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22832487816825573008063923 34248731725238359512095885)
      ·
        refine ⟨12843274396964384817035957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34248731725238359512095885 12843274396964384817035957)
        ·
          refine ⟨1204056974715411076597121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12843274396964384817035957 1204056974715411076597121)
          ·
            refine ⟨903042731036558307447841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1204056974715411076597121 903042731036558307447841)
            ·
              refine ⟨677282048277418730585881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 903042731036558307447841 677282048277418730585881)
              ·
                refine ⟨507961536208064047939411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 677282048277418730585881 507961536208064047939411)
                ·
                  refine ⟨761942304312096071909117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 507961536208064047939411 761942304312096071909117)
                  ·
                    refine ⟨285728364117036026965919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 761942304312096071909117 285728364117036026965919)
                    ·
                      rfl

theorem cell22_834681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2, 1, 3].length) (baseStart_834681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834681 prefixEnd_834681 := by exact prefixLift 834681
  have htrace : WordTrace (prefixWord ++ tailWord_834681) baseStart_834681 baseEnd_834681 := by
    simpa [prefixWord, tailWord_834681, baseEnd_834681] using wordTrace_append hprefix tailTrace_834681
  have hstable : (prefixWord ++ tailWord_834681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834681).length < 2 ^ (prefixWord ++ tailWord_834681).sum := by decide
  have hdescent : baseEnd_834681 < baseStart_834681 := by decide
  rcases family_descends (prefixWord ++ tailWord_834681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834720 : List Nat := [2, 1, 1, 4, 2, 1, 2, 2, 4, 3]
def baseStart_834720 : Nat := 118140960795 + 834720 * 2 ^ 59
def prefixEnd_834720 : Nat := 4983230072969 + 3 ^ 40 * 834720 * 2
def baseEnd_834720 : Nat := 285741714614052925240799

theorem tailTrace_834720 : CollatzResearch.WordTrace tailWord_834720 prefixEnd_834720 285741714614052925240799 := by
  unfold tailWord_834720
  simp only [CollatzResearch.WordTrace]
  refine ⟨15222369767979736835710807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20296493023972982447614409 15222369767979736835710807)
  ·
    refine ⟨22833554651969605253566211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15222369767979736835710807 22833554651969605253566211)
    ·
      refine ⟨34250331977954407880349317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22833554651969605253566211 34250331977954407880349317)
      ·
        refine ⟨6421937245866451477565497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34250331977954407880349317 6421937245866451477565497)
        ·
          refine ⟨4816452934399838608174123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6421937245866451477565497 4816452934399838608174123)
          ·
            refine ⟨7224679401599757912261185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4816452934399838608174123 7224679401599757912261185)
            ·
              refine ⟨5418509551199818434195889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7224679401599757912261185 5418509551199818434195889)
              ·
                refine ⟨4063882163399863825646917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5418509551199818434195889 4063882163399863825646917)
                ·
                  refine ⟨761977905637474467308797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4063882163399863825646917 761977905637474467308797)
                  ·
                    refine ⟨285741714614052925240799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 761977905637474467308797 285741714614052925240799)
                    ·
                      rfl

theorem cell22_834720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 4, 3].length) (baseStart_834720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834720 prefixEnd_834720 := by exact prefixLift 834720
  have htrace : WordTrace (prefixWord ++ tailWord_834720) baseStart_834720 baseEnd_834720 := by
    simpa [prefixWord, tailWord_834720, baseEnd_834720] using wordTrace_append hprefix tailTrace_834720
  have hstable : (prefixWord ++ tailWord_834720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834720).length < 2 ^ (prefixWord ++ tailWord_834720).sum := by decide
  have hdescent : baseEnd_834720 < baseStart_834720 := by decide
  rcases family_descends (prefixWord ++ tailWord_834720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834724 : List Nat := [2, 3, 1, 2, 3, 3, 2, 1, 1, 4]
def baseStart_834724 : Nat := 118140960795 + 834724 * 2 ^ 59
def prefixEnd_834724 : Nat := 4983230072969 + 3 ^ 40 * 834724 * 2
def baseEnd_834724 : Nat := 285743083895798248140787

theorem tailTrace_834724 : CollatzResearch.WordTrace tailWord_834724 prefixEnd_834724 285743083895798248140787 := by
  unfold tailWord_834724
  simp only [CollatzResearch.WordTrace]
  refine ⟨15222442713972491177283613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20296590285296654903044817 15222442713972491177283613)
  ·
    refine ⟨5708416017739684191481355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15222442713972491177283613 5708416017739684191481355)
    ·
      refine ⟨8562624026609526287222033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5708416017739684191481355 8562624026609526287222033)
      ·
        refine ⟨6421968019957144715416525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8562624026609526287222033 6421968019957144715416525)
        ·
          refine ⟨2408238007483929268281197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6421968019957144715416525 2408238007483929268281197)
          ·
            refine ⟨903089252806473475605449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2408238007483929268281197 903089252806473475605449)
            ·
              refine ⟨677316939604855106704087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 903089252806473475605449 677316939604855106704087)
              ·
                refine ⟨1015975409407282660056131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 677316939604855106704087 1015975409407282660056131)
                ·
                  refine ⟨1523963114110923990084197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1015975409407282660056131 1523963114110923990084197)
                  ·
                    refine ⟨285743083895798248140787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1523963114110923990084197 285743083895798248140787)
                    ·
                      rfl

theorem cell22_834724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_834724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834724 prefixEnd_834724 := by exact prefixLift 834724
  have htrace : WordTrace (prefixWord ++ tailWord_834724) baseStart_834724 baseEnd_834724 := by
    simpa [prefixWord, tailWord_834724, baseEnd_834724] using wordTrace_append hprefix tailTrace_834724
  have hstable : (prefixWord ++ tailWord_834724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834724).length < 2 ^ (prefixWord ++ tailWord_834724).sum := by decide
  have hdescent : baseEnd_834724 < baseStart_834724 := by decide
  rcases family_descends (prefixWord ++ tailWord_834724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834737 : List Nat := [1, 2, 2, 5, 1, 2, 1, 1, 4, 3]
def baseStart_834737 : Nat := 118140960795 + 834737 * 2 ^ 59
def prefixEnd_834737 : Nat := 4983230072969 + 3 ^ 40 * 834737 * 2
def baseEnd_834737 : Nat := 285747534061470547565747

theorem tailTrace_834737 : CollatzResearch.WordTrace tailWord_834737 prefixEnd_834737 285747534061470547565747 := by
  unfold tailWord_834737
  simp only [CollatzResearch.WordTrace]
  refine ⟨30445359576897885574790465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20296906384598590383193643 30445359576897885574790465)
  ·
    refine ⟨22834019682673414181092849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30445359576897885574790465 22834019682673414181092849)
    ·
      refine ⟨17125514762005060635819637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22834019682673414181092849 17125514762005060635819637)
      ·
        refine ⟨1605517008937974434608091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17125514762005060635819637 1605517008937974434608091)
        ·
          refine ⟨2408275513406961651912137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1605517008937974434608091 2408275513406961651912137)
          ·
            refine ⟨1806206635055221238934103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2408275513406961651912137 1806206635055221238934103)
            ·
              refine ⟨2709309952582831858401155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1806206635055221238934103 2709309952582831858401155)
              ·
                refine ⟨4063964928874247787601733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2709309952582831858401155 4063964928874247787601733)
                ·
                  refine ⟨761993424163921460175325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4063964928874247787601733 761993424163921460175325)
                  ·
                    refine ⟨285747534061470547565747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 761993424163921460175325 285747534061470547565747)
                    ·
                      rfl

theorem cell22_834737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4, 3].length) (baseStart_834737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834737 prefixEnd_834737 := by exact prefixLift 834737
  have htrace : WordTrace (prefixWord ++ tailWord_834737) baseStart_834737 baseEnd_834737 := by
    simpa [prefixWord, tailWord_834737, baseEnd_834737] using wordTrace_append hprefix tailTrace_834737
  have hstable : (prefixWord ++ tailWord_834737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834737).length < 2 ^ (prefixWord ++ tailWord_834737).sum := by decide
  have hdescent : baseEnd_834737 < baseStart_834737 := by decide
  rcases family_descends (prefixWord ++ tailWord_834737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834758 : List Nat := [6, 1, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_834758 : Nat := 118140960795 + 834758 * 2 ^ 59
def prefixEnd_834758 : Nat := 4983230072969 + 3 ^ 40 * 834758 * 2
def baseEnd_834758 : Nat := 285754722790633492790683

theorem tailTrace_834758 : CollatzResearch.WordTrace tailWord_834758 prefixEnd_834758 285754722790633492790683 := by
  unfold tailWord_834758
  simp only [CollatzResearch.WordTrace]
  refine ⟨951441422181931442540779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20297417006547870774203285 951441422181931442540779)
  ·
    refine ⟨1427162133272897163811169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 951441422181931442540779 1427162133272897163811169)
    ·
      refine ⟨1070371599954672872858377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1427162133272897163811169 1070371599954672872858377)
      ·
        refine ⟨802778699966004654643783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1070371599954672872858377 802778699966004654643783)
        ·
          refine ⟨1204168049949006981965675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 802778699966004654643783 1204168049949006981965675)
          ·
            refine ⟨1806252074923510472948513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1204168049949006981965675 1806252074923510472948513)
            ·
              refine ⟨1354689056192632854711385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1806252074923510472948513 1354689056192632854711385)
              ·
                refine ⟨1016016792144474641033539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1354689056192632854711385 1016016792144474641033539)
                ·
                  refine ⟨1524025188216711961550309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1016016792144474641033539 1524025188216711961550309)
                  ·
                    refine ⟨285754722790633492790683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1524025188216711961550309 285754722790633492790683)
                    ·
                      rfl

theorem cell22_834758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_834758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834758 prefixEnd_834758 := by exact prefixLift 834758
  have htrace : WordTrace (prefixWord ++ tailWord_834758) baseStart_834758 baseEnd_834758 := by
    simpa [prefixWord, tailWord_834758, baseEnd_834758] using wordTrace_append hprefix tailTrace_834758
  have hstable : (prefixWord ++ tailWord_834758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834758).length < 2 ^ (prefixWord ++ tailWord_834758).sum := by decide
  have hdescent : baseEnd_834758 < baseStart_834758 := by decide
  rcases family_descends (prefixWord ++ tailWord_834758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834799 : List Nat := [1, 1, 2, 1, 7, 2, 1, 1, 3, 3]
def baseStart_834799 : Nat := 118140960795 + 834799 * 2 ^ 59
def prefixEnd_834799 : Nat := 4983230072969 + 3 ^ 40 * 834799 * 2
def baseEnd_834799 : Nat := 285768757928523052515557

theorem tailTrace_834799 : CollatzResearch.WordTrace tailWord_834799 prefixEnd_834799 285768757928523052515557 := by
  unfold tailWord_834799
  simp only [CollatzResearch.WordTrace]
  refine ⟨30447620902673270163547451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20298413935115513442364967 30447620902673270163547451)
  ·
    refine ⟨45671431354009905245321177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30447620902673270163547451 45671431354009905245321177)
    ·
      refine ⟨34253573515507428933990883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45671431354009905245321177 34253573515507428933990883)
      ·
        refine ⟨51380360273261143400986325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34253573515507428933990883 51380360273261143400986325)
        ·
          refine ⟨1204227193904558048460617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 51380360273261143400986325 1204227193904558048460617)
          ·
            refine ⟨903170395428418536345463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1204227193904558048460617 903170395428418536345463)
            ·
              refine ⟨1354755593142627804518195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 903170395428418536345463 1354755593142627804518195)
              ·
                refine ⟨2032133389713941706777293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1354755593142627804518195 2032133389713941706777293)
                ·
                  refine ⟨762050021142728140041485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2032133389713941706777293 762050021142728140041485)
                  ·
                    refine ⟨285768757928523052515557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 762050021142728140041485 285768757928523052515557)
                    ·
                      rfl

theorem cell22_834799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3, 3].length) (baseStart_834799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834799 prefixEnd_834799 := by exact prefixLift 834799
  have htrace : WordTrace (prefixWord ++ tailWord_834799) baseStart_834799 baseEnd_834799 := by
    simpa [prefixWord, tailWord_834799, baseEnd_834799] using wordTrace_append hprefix tailTrace_834799
  have hstable : (prefixWord ++ tailWord_834799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834799).length < 2 ^ (prefixWord ++ tailWord_834799).sum := by decide
  have hdescent : baseEnd_834799 < baseStart_834799 := by decide
  rcases family_descends (prefixWord ++ tailWord_834799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834808 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 1, 10]
def baseStart_834808 : Nat := 118140960795 + 834808 * 2 ^ 59
def prefixEnd_834808 : Nat := 4983230072969 + 3 ^ 40 * 834808 * 2
def baseEnd_834808 : Nat := 285771838812450029040529

theorem tailTrace_834808 : CollatzResearch.WordTrace tailWord_834808 prefixEnd_834808 285771838812450029040529 := by
  unfold tailWord_834808
  simp only [CollatzResearch.WordTrace]
  refine ⟨15223974579820332350312539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20298632773093776467083385 15223974579820332350312539)
  ·
    refine ⟨22835961869730498525468809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15223974579820332350312539 22835961869730498525468809)
    ·
      refine ⟨17126971402297873894101607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22835961869730498525468809 17126971402297873894101607)
      ·
        refine ⟨25690457103446810841152411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17126971402297873894101607 25690457103446810841152411)
        ·
          refine ⟨38535685655170216261728617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25690457103446810841152411 38535685655170216261728617)
          ·
            refine ⟨28901764241377662196296463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38535685655170216261728617 28901764241377662196296463)
            ·
              refine ⟨43352646362066493294444695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28901764241377662196296463 43352646362066493294444695)
              ·
                refine ⟨65028969543099739941667043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43352646362066493294444695 65028969543099739941667043)
                ·
                  refine ⟨97543454314649609912500565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65028969543099739941667043 97543454314649609912500565)
                  ·
                    refine ⟨285771838812450029040529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 97543454314649609912500565 285771838812450029040529)
                    ·
                      rfl

theorem cell22_834808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_834808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834808 prefixEnd_834808 := by exact prefixLift 834808
  have htrace : WordTrace (prefixWord ++ tailWord_834808) baseStart_834808 baseEnd_834808 := by
    simpa [prefixWord, tailWord_834808, baseEnd_834808] using wordTrace_append hprefix tailTrace_834808
  have hstable : (prefixWord ++ tailWord_834808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834808).length < 2 ^ (prefixWord ++ tailWord_834808).sum := by decide
  have hdescent : baseEnd_834808 < baseStart_834808 := by decide
  rcases family_descends (prefixWord ++ tailWord_834808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834812 : List Nat := [2, 2, 2, 1, 5, 1, 1, 3, 5]
def baseStart_834812 : Nat := 118140960795 + 834812 * 2 ^ 59
def prefixEnd_834812 : Nat := 4983230072969 + 3 ^ 40 * 834812 * 2
def baseEnd_834812 : Nat := 95257736031398450646839

theorem tailTrace_834812 : CollatzResearch.WordTrace tailWord_834812 prefixEnd_834812 95257736031398450646839 := by
  unfold tailWord_834812
  simp only [CollatzResearch.WordTrace]
  refine ⟨15224047525813086691885345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20298730034417448922513793 15224047525813086691885345)
  ·
    refine ⟨11418035644359815018914009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15224047525813086691885345 11418035644359815018914009)
    ·
      refine ⟨8563526733269861264185507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11418035644359815018914009 8563526733269861264185507)
      ·
        refine ⟨12845290099904791896278261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8563526733269861264185507 12845290099904791896278261)
        ·
          refine ⟨1204245946866074240276087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12845290099904791896278261 1204245946866074240276087)
          ·
            refine ⟨1806368920299111360414131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1204245946866074240276087 1806368920299111360414131)
            ·
              refine ⟨2709553380448667040621197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1806368920299111360414131 2709553380448667040621197)
              ·
                refine ⟨1016082517668250140232949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2709553380448667040621197 1016082517668250140232949)
                ·
                  refine ⟨95257736031398450646839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1016082517668250140232949 95257736031398450646839)
                  ·
                    rfl

theorem cell22_834812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 5].length) (baseStart_834812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834812 prefixEnd_834812 := by exact prefixLift 834812
  have htrace : WordTrace (prefixWord ++ tailWord_834812) baseStart_834812 baseEnd_834812 := by
    simpa [prefixWord, tailWord_834812, baseEnd_834812] using wordTrace_append hprefix tailTrace_834812
  have hstable : (prefixWord ++ tailWord_834812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834812).length < 2 ^ (prefixWord ++ tailWord_834812).sum := by decide
  have hdescent : baseEnd_834812 < baseStart_834812 := by decide
  rcases family_descends (prefixWord ++ tailWord_834812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834825 : List Nat := [1, 2, 1, 1, 3, 3, 3, 1, 3, 4]
def baseStart_834825 : Nat := 118140960795 + 834825 * 2 ^ 59
def prefixEnd_834825 : Nat := 4983230072969 + 3 ^ 40 * 834825 * 2
def baseEnd_834825 : Nat := 285777658259867651365477

theorem tailTrace_834825 : CollatzResearch.WordTrace tailWord_834825 prefixEnd_834825 285777658259867651365477 := by
  unfold tailWord_834825
  simp only [CollatzResearch.WordTrace]
  refine ⟨30448569200579076603993929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20299046133719384402662619 30448569200579076603993929)
  ·
    refine ⟨22836426900434307452995447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30448569200579076603993929 22836426900434307452995447)
    ·
      refine ⟨34254640350651461179493171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22836426900434307452995447 34254640350651461179493171)
      ·
        refine ⟨51381960525977191769239757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34254640350651461179493171 51381960525977191769239757)
        ·
          refine ⟨19268235197241446913464909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51381960525977191769239757 19268235197241446913464909)
          ·
            refine ⟨7225588198965542592549341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19268235197241446913464909 7225588198965542592549341)
            ·
              refine ⟨2709595574612078472206003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7225588198965542592549341 2709595574612078472206003)
              ·
                refine ⟨4064393361918117708309005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2709595574612078472206003 4064393361918117708309005)
                ·
                  refine ⟨1524147510719294140615877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4064393361918117708309005 1524147510719294140615877)
                  ·
                    refine ⟨285777658259867651365477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1524147510719294140615877 285777658259867651365477)
                    ·
                      rfl

theorem cell22_834825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 4].length) (baseStart_834825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834825 prefixEnd_834825 := by exact prefixLift 834825
  have htrace : WordTrace (prefixWord ++ tailWord_834825) baseStart_834825 baseEnd_834825 := by
    simpa [prefixWord, tailWord_834825, baseEnd_834825] using wordTrace_append hprefix tailTrace_834825
  have hstable : (prefixWord ++ tailWord_834825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834825).length < 2 ^ (prefixWord ++ tailWord_834825).sum := by decide
  have hdescent : baseEnd_834825 < baseStart_834825 := by decide
  rcases family_descends (prefixWord ++ tailWord_834825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834846 : List Nat := [4, 3, 2, 1, 2, 1, 2, 2, 5]
def baseStart_834846 : Nat := 118140960795 + 834846 * 2 ^ 59
def prefixEnd_834846 : Nat := 4983230072969 + 3 ^ 40 * 834846 * 2
def baseEnd_834846 : Nat := 95261615663010198863471

theorem tailTrace_834846 : CollatzResearch.WordTrace tailWord_834846 prefixEnd_834846 95261615663010198863471 := by
  unfold tailWord_834846
  simp only [CollatzResearch.WordTrace]
  refine ⟨3806166891687874648813549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20299556755668664793672261 3806166891687874648813549)
  ·
    refine ⟨1427312584382952993305081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3806166891687874648813549 1427312584382952993305081)
    ·
      refine ⟨1070484438287214744978811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1427312584382952993305081 1070484438287214744978811)
      ·
        refine ⟨1605726657430822117468217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1070484438287214744978811 1605726657430822117468217)
        ·
          refine ⟨1204294993073116588101163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1605726657430822117468217 1204294993073116588101163)
          ·
            refine ⟨1806442489609674882151745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1204294993073116588101163 1806442489609674882151745)
            ·
              refine ⟨1354831867207256161613809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1806442489609674882151745 1354831867207256161613809)
              ·
                refine ⟨1016123900405442121210357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1354831867207256161613809 1016123900405442121210357)
                ·
                  refine ⟨95261615663010198863471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1016123900405442121210357 95261615663010198863471)
                  ·
                    rfl

theorem cell22_834846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_834846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834846 prefixEnd_834846 := by exact prefixLift 834846
  have htrace : WordTrace (prefixWord ++ tailWord_834846) baseStart_834846 baseEnd_834846 := by
    simpa [prefixWord, tailWord_834846, baseEnd_834846] using wordTrace_append hprefix tailTrace_834846
  have hstable : (prefixWord ++ tailWord_834846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834846).length < 2 ^ (prefixWord ++ tailWord_834846).sum := by decide
  have hdescent : baseEnd_834846 < baseStart_834846 := by decide
  rcases family_descends (prefixWord ++ tailWord_834846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834850 : List Nat := [3, 3, 1, 1, 5, 1, 2, 2, 1, 3]
def baseStart_834850 : Nat := 118140960795 + 834850 * 2 ^ 59
def prefixEnd_834850 : Nat := 4983230072969 + 3 ^ 40 * 834850 * 2
def baseEnd_834850 : Nat := 285786216270775919490401

theorem tailTrace_834850 : CollatzResearch.WordTrace tailWord_834850 prefixEnd_834850 285786216270775919490401 := by
  unfold tailWord_834850
  simp only [CollatzResearch.WordTrace]
  refine ⟨7612370256372126468413501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20299654016992337249102669 7612370256372126468413501)
  ·
    refine ⟨2854638846139547425655063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7612370256372126468413501 2854638846139547425655063)
    ·
      refine ⟨4281958269209321138482595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2854638846139547425655063 4281958269209321138482595)
      ·
        refine ⟨6422937403813981707723893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4281958269209321138482595 6422937403813981707723893)
        ·
          refine ⟨602150381607560785099115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6422937403813981707723893 602150381607560785099115)
          ·
            refine ⟨903225572411341177648673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602150381607560785099115 903225572411341177648673)
            ·
              refine ⟨677419179308505883236505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 903225572411341177648673 677419179308505883236505)
              ·
                refine ⟨508064384481379412427379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 677419179308505883236505 508064384481379412427379)
                ·
                  refine ⟨762096576722069118641069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 508064384481379412427379 762096576722069118641069)
                  ·
                    refine ⟨285786216270775919490401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 762096576722069118641069 285786216270775919490401)
                    ·
                      rfl

theorem cell22_834850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_834850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834850 prefixEnd_834850 := by exact prefixLift 834850
  have htrace : WordTrace (prefixWord ++ tailWord_834850) baseStart_834850 baseEnd_834850 := by
    simpa [prefixWord, tailWord_834850, baseEnd_834850] using wordTrace_append hprefix tailTrace_834850
  have hstable : (prefixWord ++ tailWord_834850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834850).length < 2 ^ (prefixWord ++ tailWord_834850).sum := by decide
  have hdescent : baseEnd_834850 < baseStart_834850 := by decide
  rcases family_descends (prefixWord ++ tailWord_834850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834887 : List Nat := [1, 1, 4, 1, 2, 3, 3, 1, 2, 4]
def baseStart_834887 : Nat := 118140960795 + 834887 * 2 ^ 59
def prefixEnd_834887 : Nat := 4983230072969 + 3 ^ 40 * 834887 * 2
def baseEnd_834887 : Nat := 285798882126920156315287

theorem tailTrace_834887 : CollatzResearch.WordTrace tailWord_834887 prefixEnd_834887 285798882126920156315287 := by
  unfold tailWord_834887
  simp only [CollatzResearch.WordTrace]
  refine ⟨30450830526354461192750915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20300553684236307461833943 30450830526354461192750915)
  ·
    refine ⟨45676245789531691789126373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30450830526354461192750915 45676245789531691789126373)
    ·
      refine ⟨8564296085537192210461195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45676245789531691789126373 8564296085537192210461195)
      ·
        refine ⟨12846444128305788315691793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8564296085537192210461195 12846444128305788315691793)
        ·
          refine ⟨9634833096229341236768845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12846444128305788315691793 9634833096229341236768845)
          ·
            refine ⟨3613062411086002963788317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9634833096229341236768845 3613062411086002963788317)
            ·
              refine ⟨1354898404157251111420619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3613062411086002963788317 1354898404157251111420619)
              ·
                refine ⟨2032347606235876667130929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1354898404157251111420619 2032347606235876667130929)
                ·
                  refine ⟨1524260704676907500348197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2032347606235876667130929 1524260704676907500348197)
                  ·
                    refine ⟨285798882126920156315287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1524260704676907500348197 285798882126920156315287)
                    ·
                      rfl

theorem cell22_834887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_834887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834887 prefixEnd_834887 := by exact prefixLift 834887
  have htrace : WordTrace (prefixWord ++ tailWord_834887) baseStart_834887 baseEnd_834887 := by
    simpa [prefixWord, tailWord_834887, baseEnd_834887] using wordTrace_append hprefix tailTrace_834887
  have hstable : (prefixWord ++ tailWord_834887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834887).length < 2 ^ (prefixWord ++ tailWord_834887).sum := by decide
  have hdescent : baseEnd_834887 < baseStart_834887 := by decide
  rcases family_descends (prefixWord ++ tailWord_834887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834951 : List Nat := [1, 1, 4, 2, 2, 2, 3, 3, 1, 3]
def baseStart_834951 : Nat := 118140960795 + 834951 * 2 ^ 59
def prefixEnd_834951 : Nat := 4983230072969 + 3 ^ 40 * 834951 * 2
def baseEnd_834951 : Nat := 285820790634845322715091

theorem tailTrace_834951 : CollatzResearch.WordTrace tailWord_834951 prefixEnd_834951 285820790634845322715091 := by
  unfold tailWord_834951
  simp only [CollatzResearch.WordTrace]
  refine ⟨30453164798122600123080707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20302109865415066748720471 30453164798122600123080707)
  ·
    refine ⟨45679747197183900184621061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30453164798122600123080707 45679747197183900184621061)
    ·
      refine ⟨8564952599471981284616449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45679747197183900184621061 8564952599471981284616449)
      ·
        refine ⟨6423714449603985963462337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8564952599471981284616449 6423714449603985963462337)
        ·
          refine ⟨4817785837202989472596753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6423714449603985963462337 4817785837202989472596753)
          ·
            refine ⟨3613339377902242104447565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4817785837202989472596753 3613339377902242104447565)
            ·
              refine ⟨1355002266713340789167837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3613339377902242104447565 1355002266713340789167837)
              ·
                refine ⟨508125850017502795937939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1355002266713340789167837 508125850017502795937939)
                ·
                  refine ⟨762188775026254193906909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 508125850017502795937939 762188775026254193906909)
                  ·
                    refine ⟨285820790634845322715091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 762188775026254193906909 285820790634845322715091)
                    ·
                      rfl

theorem cell22_834951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_834951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834951 prefixEnd_834951 := by exact prefixLift 834951
  have htrace : WordTrace (prefixWord ++ tailWord_834951) baseStart_834951 baseEnd_834951 := by
    simpa [prefixWord, tailWord_834951, baseEnd_834951] using wordTrace_append hprefix tailTrace_834951
  have hstable : (prefixWord ++ tailWord_834951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834951).length < 2 ^ (prefixWord ++ tailWord_834951).sum := by decide
  have hdescent : baseEnd_834951 < baseStart_834951 := by decide
  rcases family_descends (prefixWord ++ tailWord_834951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834968 : List Nat := [2, 1, 2, 5, 3, 1, 1, 1, 3, 3]
def baseStart_834968 : Nat := 118140960795 + 834968 * 2 ^ 59
def prefixEnd_834968 : Nat := 4983230072969 + 3 ^ 40 * 834968 * 2
def baseEnd_834968 : Nat := 285826610082262945040039

theorem tailTrace_834968 : CollatzResearch.WordTrace tailWord_834968 prefixEnd_834968 285826610082262945040039 := by
  unfold tailWord_834968
  simp only [CollatzResearch.WordTrace]
  refine ⟨15226892419530506013224779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20302523226040674684299705 15226892419530506013224779)
  ·
    refine ⟨22840338629295759019837169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15226892419530506013224779 22840338629295759019837169)
    ·
      refine ⟨17130253971971819264877877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22840338629295759019837169 17130253971971819264877877)
      ·
        refine ⟨1605961309872358056082301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17130253971971819264877877 1605961309872358056082301)
        ·
          refine ⟨602235491202134271030863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1605961309872358056082301 602235491202134271030863)
          ·
            refine ⟨903353236803201406546295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602235491202134271030863 903353236803201406546295)
            ·
              refine ⟨1355029855204802109819443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 903353236803201406546295 1355029855204802109819443)
              ·
                refine ⟨2032544782807203164729165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1355029855204802109819443 2032544782807203164729165)
                ·
                  refine ⟨762204293552701186773437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2032544782807203164729165 762204293552701186773437)
                  ·
                    refine ⟨285826610082262945040039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 762204293552701186773437 285826610082262945040039)
                    ·
                      rfl

theorem cell22_834968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 3, 3].length) (baseStart_834968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_834968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_834968 prefixEnd_834968 := by exact prefixLift 834968
  have htrace : WordTrace (prefixWord ++ tailWord_834968) baseStart_834968 baseEnd_834968 := by
    simpa [prefixWord, tailWord_834968, baseEnd_834968] using wordTrace_append hprefix tailTrace_834968
  have hstable : (prefixWord ++ tailWord_834968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834968).length < 2 ^ (prefixWord ++ tailWord_834968).sum := by decide
  have hdescent : baseEnd_834968 < baseStart_834968 := by decide
  rcases family_descends (prefixWord ++ tailWord_834968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835007 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 6, 3]
def baseStart_835007 : Nat := 118140960795 + 835007 * 2 ^ 59
def prefixEnd_835007 : Nat := 4983230072969 + 3 ^ 40 * 835007 * 2
def baseEnd_835007 : Nat := 285839960579279843314919

theorem tailTrace_835007 : CollatzResearch.WordTrace tailWord_835007 prefixEnd_835007 285839960579279843314919 := by
  unfold tailWord_835007
  simp only [CollatzResearch.WordTrace]
  refine ⟨30455207285919721687119275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20303471523946481124746183 30455207285919721687119275)
  ·
    refine ⟨45682810928879582530678913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30455207285919721687119275 45682810928879582530678913)
    ·
      refine ⟨34262108196659686898009185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45682810928879582530678913 34262108196659686898009185)
      ·
        refine ⟨25696581147494765173506889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34262108196659686898009185 25696581147494765173506889)
        ·
          refine ⟨19272435860621073880130167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25696581147494765173506889 19272435860621073880130167)
          ·
            refine ⟨28908653790931610820195251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19272435860621073880130167 28908653790931610820195251)
            ·
              refine ⟨43362980686397416230292877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28908653790931610820195251 43362980686397416230292877)
              ·
                refine ⟨16261117757399031086359829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43362980686397416230292877 16261117757399031086359829)
                ·
                  refine ⟨762239894878079582173117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16261117757399031086359829 762239894878079582173117)
                  ·
                    refine ⟨285839960579279843314919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 762239894878079582173117 285839960579279843314919)
                    ·
                      rfl

theorem cell22_835007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6, 3].length) (baseStart_835007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_835007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_835007 prefixEnd_835007 := by exact prefixLift 835007
  have htrace : WordTrace (prefixWord ++ tailWord_835007) baseStart_835007 baseEnd_835007 := by
    simpa [prefixWord, tailWord_835007, baseEnd_835007] using wordTrace_append hprefix tailTrace_835007
  have hstable : (prefixWord ++ tailWord_835007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835007).length < 2 ^ (prefixWord ++ tailWord_835007).sum := by decide
  have hdescent : baseEnd_835007 < baseStart_835007 := by decide
  rcases family_descends (prefixWord ++ tailWord_835007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835054 : List Nat := [4, 1, 2, 1, 2, 1, 5, 6]
def baseStart_835054 : Nat := 118140960795 + 835054 * 2 ^ 59
def prefixEnd_835054 : Nat := 4983230072969 + 3 ^ 40 * 835054 * 2
def baseEnd_835054 : Nat := 31761783293309709709975

theorem tailTrace_835054 : CollatzResearch.WordTrace tailWord_835054 prefixEnd_835054 31761783293309709709975 := by
  unfold tailWord_835054
  simp only [CollatzResearch.WordTrace]
  refine ⟨3807115189593681089260027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20304614344499632476053477 3807115189593681089260027)
  ·
    refine ⟨5710672784390521633890041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3807115189593681089260027 5710672784390521633890041)
    ·
      refine ⟨4283004588292891225417531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5710672784390521633890041 4283004588292891225417531)
      ·
        refine ⟨6424506882439336838126297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4283004588292891225417531 6424506882439336838126297)
        ·
          refine ⟨4818380161829502628594723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6424506882439336838126297 4818380161829502628594723)
          ·
            refine ⟨7227570242744253942892085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4818380161829502628594723 7227570242744253942892085)
            ·
              refine ⟨677584710257273807146133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7227570242744253942892085 677584710257273807146133)
              ·
                refine ⟨31761783293309709709975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 677584710257273807146133 31761783293309709709975)
                ·
                  rfl

theorem cell22_835054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 6].length) (baseStart_835054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_835054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_835054 prefixEnd_835054 := by exact prefixLift 835054
  have htrace : WordTrace (prefixWord ++ tailWord_835054) baseStart_835054 baseEnd_835054 := by
    simpa [prefixWord, tailWord_835054, baseEnd_835054] using wordTrace_append hprefix tailTrace_835054
  have hstable : (prefixWord ++ tailWord_835054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835054).length < 2 ^ (prefixWord ++ tailWord_835054).sum := by decide
  have hdescent : baseEnd_835054 < baseStart_835054 := by decide
  rcases family_descends (prefixWord ++ tailWord_835054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835176 : List Nat := [2, 1, 4, 3, 1, 2, 1, 2, 1, 5]
def baseStart_835176 : Nat := 118140960795 + 835176 * 2 ^ 59
def prefixEnd_835176 : Nat := 4983230072969 + 3 ^ 40 * 835176 * 2
def baseEnd_835176 : Nat := 285897812733019735839401

theorem tailTrace_835176 : CollatzResearch.WordTrace tailWord_835176 prefixEnd_835176 285897812733019735839401 := by
  unfold tailWord_835176
  simp only [CollatzResearch.WordTrace]
  refine ⟨15230685611153731775010691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20307580814871642366680921 15230685611153731775010691)
  ·
    refine ⟨22846028416730597662516037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15230685611153731775010691 22846028416730597662516037)
    ·
      refine ⟨4283630328136987061721757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22846028416730597662516037 4283630328136987061721757)
      ·
        refine ⟨1606361373051370148145659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4283630328136987061721757 1606361373051370148145659)
        ·
          refine ⟨2409542059577055222218489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1606361373051370148145659 2409542059577055222218489)
          ·
            refine ⟨1807156544682791416663867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2409542059577055222218489 1807156544682791416663867)
            ·
              refine ⟨2710734817024187124995801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1807156544682791416663867 2710734817024187124995801)
              ·
                refine ⟨2033051112768140343746851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2710734817024187124995801 2033051112768140343746851)
                ·
                  refine ⟨3049576669152210515620277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2033051112768140343746851 3049576669152210515620277)
                  ·
                    refine ⟨285897812733019735839401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3049576669152210515620277 285897812733019735839401)
                    ·
                      rfl

theorem cell22_835176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_835176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_835176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_835176 prefixEnd_835176 := by exact prefixLift 835176
  have htrace : WordTrace (prefixWord ++ tailWord_835176) baseStart_835176 baseEnd_835176 := by
    simpa [prefixWord, tailWord_835176, baseEnd_835176] using wordTrace_append hprefix tailTrace_835176
  have hstable : (prefixWord ++ tailWord_835176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835176).length < 2 ^ (prefixWord ++ tailWord_835176).sum := by decide
  have hdescent : baseEnd_835176 < baseStart_835176 := by decide
  rcases family_descends (prefixWord ++ tailWord_835176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835187 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 4, 7]
def baseStart_835187 : Nat := 118140960795 + 835187 * 2 ^ 59
def prefixEnd_835187 : Nat := 4983230072969 + 3 ^ 40 * 835187 * 2
def baseEnd_835187 : Nat := 285901578257819373814367

theorem tailTrace_835187 : CollatzResearch.WordTrace tailWord_835187 prefixEnd_835187 285901578257819373814367 := by
  unfold tailWord_835187
  simp only [CollatzResearch.WordTrace]
  refine ⟨30461772425267612428671815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20307848283511741619114543 30461772425267612428671815)
  ·
    refine ⟨45692658637901418643007723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30461772425267612428671815 45692658637901418643007723)
    ·
      refine ⟨68538987956852127964511585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45692658637901418643007723 68538987956852127964511585)
      ·
        refine ⟨51404240967639095973383689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68538987956852127964511585 51404240967639095973383689)
        ·
          refine ⟨38553180725729321980037767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51404240967639095973383689 38553180725729321980037767)
          ·
            refine ⟨57829771088593982970056651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38553180725729321980037767 57829771088593982970056651)
            ·
              refine ⟨86744656632890974455084977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57829771088593982970056651 86744656632890974455084977)
              ·
                refine ⟨65058492474668230841313733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86744656632890974455084977 65058492474668230841313733)
                ·
                  refine ⟨12198467339000293282746325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65058492474668230841313733 12198467339000293282746325)
                  ·
                    refine ⟨285901578257819373814367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12198467339000293282746325 285901578257819373814367)
                    ·
                      rfl

theorem cell22_835187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 7].length) (baseStart_835187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_835187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_835187 prefixEnd_835187 := by exact prefixLift 835187
  have htrace : WordTrace (prefixWord ++ tailWord_835187) baseStart_835187 baseEnd_835187 := by
    simpa [prefixWord, tailWord_835187, baseEnd_835187] using wordTrace_append hprefix tailTrace_835187
  have hstable : (prefixWord ++ tailWord_835187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835187).length < 2 ^ (prefixWord ++ tailWord_835187).sum := by decide
  have hdescent : baseEnd_835187 < baseStart_835187 := by decide
  rcases family_descends (prefixWord ++ tailWord_835187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835189 : List Nat := [1, 3, 4, 2, 1, 11]
def baseStart_835189 : Nat := 118140960795 + 835189 * 2 ^ 59
def prefixEnd_835189 : Nat := 4983230072969 + 3 ^ 40 * 835189 * 2
def baseEnd_835189 : Nat := 3529657566650518953881

theorem tailTrace_835189 : CollatzResearch.WordTrace tailWord_835189 prefixEnd_835189 3529657566650518953881 := by
  unfold tailWord_835189
  simp only [CollatzResearch.WordTrace]
  refine ⟨30461845371260366770244621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20307896914173577846829747 30461845371260366770244621)
  ·
    refine ⟨11423192014222637538841733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30461845371260366770244621 11423192014222637538841733)
    ·
      refine ⟨2141848502666744538532825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11423192014222637538841733 2141848502666744538532825)
      ·
        refine ⟨1606386377000058403899619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2141848502666744538532825 1606386377000058403899619)
        ·
          refine ⟨2409579565500087605849429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1606386377000058403899619 2409579565500087605849429)
          ·
            refine ⟨3529657566650518953881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2409579565500087605849429 3529657566650518953881)
            ·
              rfl

theorem cell22_835189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 11].length) (baseStart_835189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_835189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_835189 prefixEnd_835189 := by exact prefixLift 835189
  have htrace : WordTrace (prefixWord ++ tailWord_835189) baseStart_835189 baseEnd_835189 := by
    simpa [prefixWord, tailWord_835189, baseEnd_835189] using wordTrace_append hprefix tailTrace_835189
  have hstable : (prefixWord ++ tailWord_835189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835189).length < 2 ^ (prefixWord ++ tailWord_835189).sum := by decide
  have hdescent : baseEnd_835189 < baseStart_835189 := by decide
  rcases family_descends (prefixWord ++ tailWord_835189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835268 : List Nat := [2, 3, 3, 1, 1, 1, 5, 1, 5]
def baseStart_835268 : Nat := 118140960795 + 835268 * 2 ^ 59
def prefixEnd_835268 : Nat := 4983230072969 + 3 ^ 40 * 835268 * 2
def baseEnd_835268 : Nat := 95309768737720720846373

theorem tailTrace_835268 : CollatzResearch.WordTrace tailWord_835268 prefixEnd_835268 95309768737720720846373 := by
  unfold tailWord_835268
  simp only [CollatzResearch.WordTrace]
  refine ⟨15232363368987081631185229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20309817825316108841580305 15232363368987081631185229)
  ·
    refine ⟨5712136263370155611694461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15232363368987081631185229 5712136263370155611694461)
    ·
      refine ⟨2142051098763808354385423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5712136263370155611694461 2142051098763808354385423)
      ·
        refine ⟨3213076648145712531578135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2142051098763808354385423 3213076648145712531578135)
        ·
          refine ⟨4819614972218568797367203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3213076648145712531578135 4819614972218568797367203)
          ·
            refine ⟨7229422458327853196050805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4819614972218568797367203 7229422458327853196050805)
            ·
              refine ⟨677758355468236237129763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7229422458327853196050805 677758355468236237129763)
              ·
                refine ⟨1016637533202354355694645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 677758355468236237129763 1016637533202354355694645)
                ·
                  refine ⟨95309768737720720846373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1016637533202354355694645 95309768737720720846373)
                  ·
                    rfl

theorem cell22_835268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_835268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_835268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_835268 prefixEnd_835268 := by exact prefixLift 835268
  have htrace : WordTrace (prefixWord ++ tailWord_835268) baseStart_835268 baseEnd_835268 := by
    simpa [prefixWord, tailWord_835268, baseEnd_835268] using wordTrace_append hprefix tailTrace_835268
  have hstable : (prefixWord ++ tailWord_835268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835268).length < 2 ^ (prefixWord ++ tailWord_835268).sum := by decide
  have hdescent : baseEnd_835268 < baseStart_835268 := by decide
  rcases family_descends (prefixWord ++ tailWord_835268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835281 : List Nat := [1, 2, 2, 1, 2, 4, 1, 4, 1, 4]
def baseStart_835281 : Nat := 118140960795 + 835281 * 2 ^ 59
def prefixEnd_835281 : Nat := 4983230072969 + 3 ^ 40 * 835281 * 2
def baseEnd_835281 : Nat := 285933756378834461964079

theorem tailTrace_835281 : CollatzResearch.WordTrace tailWord_835281 prefixEnd_835281 285933756378834461964079 := by
  unfold tailWord_835281
  simp only [CollatzResearch.WordTrace]
  refine ⟨30465200886927066482593697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20310133924618044321729131 30465200886927066482593697)
  ·
    refine ⟨22848900665195299861945273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30465200886927066482593697 22848900665195299861945273)
    ·
      refine ⟨17136675498896474896458955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22848900665195299861945273 17136675498896474896458955)
      ·
        refine ⟨25705013248344712344688433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17136675498896474896458955 25705013248344712344688433)
        ·
          refine ⟨19278759936258534258516325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25705013248344712344688433 19278759936258534258516325)
          ·
            refine ⟨3614767488048475173471811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19278759936258534258516325 3614767488048475173471811)
            ·
              refine ⟨5422151232072712760207717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3614767488048475173471811 5422151232072712760207717)
              ·
                refine ⟨1016653356013633642538947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5422151232072712760207717 1016653356013633642538947)
                ·
                  refine ⟨1524980034020450463808421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1016653356013633642538947 1524980034020450463808421)
                  ·
                    refine ⟨285933756378834461964079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1524980034020450463808421 285933756378834461964079)
                    ·
                      rfl

theorem cell22_835281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_835281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_835281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_835281 prefixEnd_835281 := by exact prefixLift 835281
  have htrace : WordTrace (prefixWord ++ tailWord_835281) baseStart_835281 baseEnd_835281 := by
    simpa [prefixWord, tailWord_835281, baseEnd_835281] using wordTrace_append hprefix tailTrace_835281
  have hstable : (prefixWord ++ tailWord_835281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835281).length < 2 ^ (prefixWord ++ tailWord_835281).sum := by decide
  have hdescent : baseEnd_835281 < baseStart_835281 := by decide
  rcases family_descends (prefixWord ++ tailWord_835281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835311 : List Nat := [1, 1, 2, 1, 5, 1, 1, 3, 4, 3]
def baseStart_835311 : Nat := 118140960795 + 835311 * 2 ^ 59
def prefixEnd_835311 : Nat := 4983230072969 + 3 ^ 40 * 835311 * 2
def baseEnd_835311 : Nat := 285944025991924383713987

theorem tailTrace_835311 : CollatzResearch.WordTrace tailWord_835311 prefixEnd_835311 285944025991924383713987 := by
  unfold tailWord_835311
  simp only [CollatzResearch.WordTrace]
  refine ⟨30466295076818381606185787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20310863384545587737457191 30466295076818381606185787)
  ·
    refine ⟨45699442615227572409278681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30466295076818381606185787 45699442615227572409278681)
    ·
      refine ⟨34274581961420679306959011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45699442615227572409278681 34274581961420679306959011)
      ·
        refine ⟨51411872942131018960438517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34274581961420679306959011 51411872942131018960438517)
        ·
          refine ⟨4819863088324783027541111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51411872942131018960438517 4819863088324783027541111)
          ·
            refine ⟨7229794632487174541311667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4819863088324783027541111 7229794632487174541311667)
            ·
              refine ⟨10844691948730761811967501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7229794632487174541311667 10844691948730761811967501)
              ·
                refine ⟨4066759480774035679487813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10844691948730761811967501 4066759480774035679487813)
                ·
                  refine ⟨762517402645131689903965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4066759480774035679487813 762517402645131689903965)
                  ·
                    refine ⟨285944025991924383713987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 762517402645131689903965 285944025991924383713987)
                    ·
                      rfl

theorem cell22_835311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4, 3].length) (baseStart_835311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_835311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_835311 prefixEnd_835311 := by exact prefixLift 835311
  have htrace : WordTrace (prefixWord ++ tailWord_835311) baseStart_835311 baseEnd_835311 := by
    simpa [prefixWord, tailWord_835311, baseEnd_835311] using wordTrace_append hprefix tailTrace_835311
  have hstable : (prefixWord ++ tailWord_835311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835311).length < 2 ^ (prefixWord ++ tailWord_835311).sum := by decide
  have hdescent : baseEnd_835311 < baseStart_835311 := by decide
  rcases family_descends (prefixWord ++ tailWord_835311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835339 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 2, 7]
def baseStart_835339 : Nat := 118140960795 + 835339 * 2 ^ 59
def prefixEnd_835339 : Nat := 4983230072969 + 3 ^ 40 * 835339 * 2
def baseEnd_835339 : Nat := 285953610964141644013901

theorem tailTrace_835339 : CollatzResearch.WordTrace tailWord_835339 prefixEnd_835339 285953610964141644013901 := by
  unfold tailWord_835339
  simp only [CollatzResearch.WordTrace]
  refine ⟨30467316320716942388205071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20311544213811294925470047 30467316320716942388205071)
  ·
    refine ⟨45700974481075413582307607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30467316320716942388205071 45700974481075413582307607)
    ·
      refine ⟨68551461721613120373461411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45700974481075413582307607 68551461721613120373461411)
      ·
        refine ⟨102827192582419680560192117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68551461721613120373461411 102827192582419680560192117)
        ·
          refine ⟨9640049304601845052518011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102827192582419680560192117 9640049304601845052518011)
          ·
            refine ⟨14460073956902767578777017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9640049304601845052518011 14460073956902767578777017)
            ·
              refine ⟨10845055467677075684082763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14460073956902767578777017 10845055467677075684082763)
              ·
                refine ⟨16267583201515613526124145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10845055467677075684082763 16267583201515613526124145)
                ·
                  refine ⟨12200687401136710144593109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16267583201515613526124145 12200687401136710144593109)
                  ·
                    refine ⟨285953610964141644013901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12200687401136710144593109 285953610964141644013901)
                    ·
                      rfl

theorem cell22_835339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 7].length) (baseStart_835339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_835339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_835339 prefixEnd_835339 := by exact prefixLift 835339
  have htrace : WordTrace (prefixWord ++ tailWord_835339) baseStart_835339 baseEnd_835339 := by
    simpa [prefixWord, tailWord_835339, baseEnd_835339] using wordTrace_append hprefix tailTrace_835339
  have hstable : (prefixWord ++ tailWord_835339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835339).length < 2 ^ (prefixWord ++ tailWord_835339).sum := by decide
  have hdescent : baseEnd_835339 < baseStart_835339 := by decide
  rcases family_descends (prefixWord ++ tailWord_835339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835358 : List Nat := [4, 3, 2, 2, 11]
def baseStart_835358 : Nat := 118140960795 + 835358 * 2 ^ 59
def prefixEnd_835358 : Nat := 4983230072969 + 3 ^ 40 * 835358 * 2
def baseEnd_835358 : Nat := 1176790596923588180201

theorem tailTrace_835358 : CollatzResearch.WordTrace tailWord_835358 prefixEnd_835358 1176790596923588180201 := by
  unfold tailWord_835358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3808501163456013579143341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20312006205098739088764485 3808501163456013579143341)
  ·
    refine ⟨1428187936296005092178753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3808501163456013579143341 1428187936296005092178753)
    ·
      refine ⟨1071140952222003819134065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1428187936296005092178753 1071140952222003819134065)
      ·
        refine ⟨803355714166502864350549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1071140952222003819134065 803355714166502864350549)
        ·
          refine ⟨1176790596923588180201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 803355714166502864350549 1176790596923588180201)
          ·
            rfl

theorem cell22_835358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 11].length) (baseStart_835358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_835358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_835358 prefixEnd_835358 := by exact prefixLift 835358
  have htrace : WordTrace (prefixWord ++ tailWord_835358) baseStart_835358 baseEnd_835358 := by
    simpa [prefixWord, tailWord_835358, baseEnd_835358] using wordTrace_append hprefix tailTrace_835358
  have hstable : (prefixWord ++ tailWord_835358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835358).length < 2 ^ (prefixWord ++ tailWord_835358).sum := by decide
  have hdescent : baseEnd_835358 < baseStart_835358 := by decide
  rcases family_descends (prefixWord ++ tailWord_835358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835390 : List Nat := [4, 2, 1, 2, 2, 2, 1, 2, 3, 3]
def baseStart_835390 : Nat := 118140960795 + 835390 * 2 ^ 59
def prefixEnd_835390 : Nat := 4983230072969 + 3 ^ 40 * 835390 * 2
def baseEnd_835390 : Nat := 285971069306394510988745

theorem tailTrace_835390 : CollatzResearch.WordTrace tailWord_835390 prefixEnd_835390 285971069306394510988745 := by
  unfold tailWord_835390
  simp only [CollatzResearch.WordTrace]
  refine ⟨3808647055441522262288953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20312784295688118732207749 3808647055441522262288953)
  ·
    refine ⟨2856485291581141696716715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3808647055441522262288953 2856485291581141696716715)
    ·
      refine ⟨4284727937371712545075073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2856485291581141696716715 4284727937371712545075073)
      ·
        refine ⟨3213545953028784408806305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4284727937371712545075073 3213545953028784408806305)
        ·
          refine ⟨2410159464771588306604729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3213545953028784408806305 2410159464771588306604729)
          ·
            refine ⟨1807619598578691229953547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2410159464771588306604729 1807619598578691229953547)
            ·
              refine ⟨2711429397868036844930321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1807619598578691229953547 2711429397868036844930321)
              ·
                refine ⟨2033572048401027633697741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2711429397868036844930321 2033572048401027633697741)
                ·
                  refine ⟨762589518150385362636653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2033572048401027633697741 762589518150385362636653)
                  ·
                    refine ⟨285971069306394510988745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 762589518150385362636653 285971069306394510988745)
                    ·
                      rfl

theorem cell22_835390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_835390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_835390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_835390 prefixEnd_835390 := by exact prefixLift 835390
  have htrace : WordTrace (prefixWord ++ tailWord_835390) baseStart_835390 baseEnd_835390 := by
    simpa [prefixWord, tailWord_835390, baseEnd_835390] using wordTrace_append hprefix tailTrace_835390
  have hstable : (prefixWord ++ tailWord_835390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835390).length < 2 ^ (prefixWord ++ tailWord_835390).sum := by decide
  have hdescent : baseEnd_835390 < baseStart_835390 := by decide
  rcases family_descends (prefixWord ++ tailWord_835390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835461 : List Nat := [1, 3, 1, 1, 3, 2, 1, 3, 1, 6]
def baseStart_835461 : Nat := 118140960795 + 835461 * 2 ^ 59
def prefixEnd_835461 : Nat := 4983230072969 + 3 ^ 40 * 835461 * 2
def baseEnd_835461 : Nat := 285995374057373992463527

theorem tailTrace_835461 : CollatzResearch.WordTrace tailWord_835461 prefixEnd_835461 285995374057373992463527 := by
  unfold tailWord_835461
  simp only [CollatzResearch.WordTrace]
  refine ⟨30471766026274957224146237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20314510684183304816097491 30471766026274957224146237)
  ·
    refine ⟨11426912259853108959054839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30471766026274957224146237 11426912259853108959054839)
    ·
      refine ⟨17140368389779663438582259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11426912259853108959054839 17140368389779663438582259)
      ·
        refine ⟨25710552584669495157873389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17140368389779663438582259 25710552584669495157873389)
        ·
          refine ⟨9641457219251060684202521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25710552584669495157873389 9641457219251060684202521)
          ·
            refine ⟨7231092914438295513151891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9641457219251060684202521 7231092914438295513151891)
            ·
              refine ⟨10846639371657443269727837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7231092914438295513151891 10846639371657443269727837)
              ·
                refine ⟨4067489764371541226147939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10846639371657443269727837 4067489764371541226147939)
                ·
                  refine ⟨6101234646557311839221909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4067489764371541226147939 6101234646557311839221909)
                  ·
                    refine ⟨285995374057373992463527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6101234646557311839221909 285995374057373992463527)
                    ·
                      rfl

theorem cell22_835461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_835461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_835461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_835461 prefixEnd_835461 := by exact prefixLift 835461
  have htrace : WordTrace (prefixWord ++ tailWord_835461) baseStart_835461 baseEnd_835461 := by
    simpa [prefixWord, tailWord_835461, baseEnd_835461] using wordTrace_append hprefix tailTrace_835461
  have hstable : (prefixWord ++ tailWord_835461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835461).length < 2 ^ (prefixWord ++ tailWord_835461).sum := by decide
  have hdescent : baseEnd_835461 < baseStart_835461 := by decide
  rcases family_descends (prefixWord ++ tailWord_835461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835482 : List Nat := [3, 1, 1, 4, 2, 2, 3, 2, 4]
def baseStart_835482 : Nat := 118140960795 + 835482 * 2 ^ 59
def prefixEnd_835482 : Nat := 4983230072969 + 3 ^ 40 * 835482 * 2
def baseEnd_835482 : Nat := 95334187595512312562821

theorem tailTrace_835482 : CollatzResearch.WordTrace tailWord_835482 prefixEnd_835482 95334187595512312562821 := by
  unfold tailWord_835482
  simp only [CollatzResearch.WordTrace]
  refine ⟨7618132989799719452665175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20315021306132585207107133 7618132989799719452665175)
  ·
    refine ⟨11427199484699579178997763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7618132989799719452665175 11427199484699579178997763)
    ·
      refine ⟨17140799227049368768496645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11427199484699579178997763 17140799227049368768496645)
      ·
        refine ⟨3213899855071756644093121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17140799227049368768496645 3213899855071756644093121)
        ·
          refine ⟨2410424891303817483069841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3213899855071756644093121 2410424891303817483069841)
          ·
            refine ⟨1807818668477863112302381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2410424891303817483069841 1807818668477863112302381)
            ·
              refine ⟨677932000679198667113393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1807818668477863112302381 677932000679198667113393)
              ·
                refine ⟨508449000509399000335045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 677932000679198667113393 508449000509399000335045)
                ·
                  refine ⟨95334187595512312562821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 508449000509399000335045 95334187595512312562821)
                  ·
                    rfl

theorem cell22_835482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2, 4].length) (baseStart_835482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_835482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_835482 prefixEnd_835482 := by exact prefixLift 835482
  have htrace : WordTrace (prefixWord ++ tailWord_835482) baseStart_835482 baseEnd_835482 := by
    simpa [prefixWord, tailWord_835482, baseEnd_835482] using wordTrace_append hprefix tailTrace_835482
  have hstable : (prefixWord ++ tailWord_835482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835482).length < 2 ^ (prefixWord ++ tailWord_835482).sum := by decide
  have hdescent : baseEnd_835482 < baseStart_835482 := by decide
  rcases family_descends (prefixWord ++ tailWord_835482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835568 : List Nat := [2, 1, 1, 1, 3, 2, 4, 1, 3, 4]
def baseStart_835568 : Nat := 118140960795 + 835568 * 2 ^ 59
def prefixEnd_835568 : Nat := 4983230072969 + 3 ^ 40 * 835568 * 2
def baseEnd_835568 : Nat := 286032002344061380038199

theorem tailTrace_835568 : CollatzResearch.WordTrace tailWord_835568 prefixEnd_835568 286032002344061380038199 := by
  unfold tailWord_835568
  simp only [CollatzResearch.WordTrace]
  refine ⟨15237834318443657249145679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20317112424591542998860905 15237834318443657249145679)
  ·
    refine ⟨22856751477665485873718519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15237834318443657249145679 22856751477665485873718519)
    ·
      refine ⟨34285127216498228810577779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22856751477665485873718519 34285127216498228810577779)
      ·
        refine ⟨51427690824747343215866669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34285127216498228810577779 51427690824747343215866669)
        ·
          refine ⟨19285384059280253705950001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51427690824747343215866669 19285384059280253705950001)
          ·
            refine ⟨14464038044460190279462501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19285384059280253705950001 14464038044460190279462501)
            ·
              refine ⟨2712007133336285677399219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14464038044460190279462501 2712007133336285677399219)
              ·
                refine ⟨4068010700004428516098829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2712007133336285677399219 4068010700004428516098829)
                ·
                  refine ⟨1525504012501660693537061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4068010700004428516098829 1525504012501660693537061)
                  ·
                    refine ⟨286032002344061380038199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1525504012501660693537061 286032002344061380038199)
                    ·
                      rfl

theorem cell22_835568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 3, 4].length) (baseStart_835568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_835568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_835568 prefixEnd_835568 := by exact prefixLift 835568
  have htrace : WordTrace (prefixWord ++ tailWord_835568) baseStart_835568 baseEnd_835568 := by
    simpa [prefixWord, tailWord_835568, baseEnd_835568] using wordTrace_append hprefix tailTrace_835568
  have hstable : (prefixWord ++ tailWord_835568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835568).length < 2 ^ (prefixWord ++ tailWord_835568).sum := by decide
  have hdescent : baseEnd_835568 < baseStart_835568 := by decide
  rcases family_descends (prefixWord ++ tailWord_835568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835585 : List Nat := [1, 2, 4, 1, 2, 1, 3, 3, 1, 4]
def baseStart_835585 : Nat := 118140960795 + 835585 * 2 ^ 59
def prefixEnd_835585 : Nat := 4983230072969 + 3 ^ 40 * 835585 * 2
def baseEnd_835585 : Nat := 286037821791479002363147

theorem tailTrace_835585 : CollatzResearch.WordTrace tailWord_835585 prefixEnd_835585 286037821791479002363147 := by
  unfold tailWord_835585
  simp only [CollatzResearch.WordTrace]
  refine ⟨30476288677825726401660209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20317525785217150934440139 30476288677825726401660209)
  ·
    refine ⟨22857216508369294801245157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30476288677825726401660209 22857216508369294801245157)
    ·
      refine ⟨4285728095319242775233467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22857216508369294801245157 4285728095319242775233467)
      ·
        refine ⟨6428592142978864162850201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4285728095319242775233467 6428592142978864162850201)
        ·
          refine ⟨4821444107234148122137651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6428592142978864162850201 4821444107234148122137651)
          ·
            refine ⟨7232166160851222183206477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4821444107234148122137651 7232166160851222183206477)
            ·
              refine ⟨2712062310319208318702429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7232166160851222183206477 2712062310319208318702429)
              ·
                refine ⟨1017023366369703119513411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2712062310319208318702429 1017023366369703119513411)
                ·
                  refine ⟨1525535049554554679270117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1017023366369703119513411 1525535049554554679270117)
                  ·
                    refine ⟨286037821791479002363147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1525535049554554679270117 286037821791479002363147)
                    ·
                      rfl

theorem cell22_835585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_835585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_835585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_835585 prefixEnd_835585 := by exact prefixLift 835585
  have htrace : WordTrace (prefixWord ++ tailWord_835585) baseStart_835585 baseEnd_835585 := by
    simpa [prefixWord, tailWord_835585, baseEnd_835585] using wordTrace_append hprefix tailTrace_835585
  have hstable : (prefixWord ++ tailWord_835585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835585).length < 2 ^ (prefixWord ++ tailWord_835585).sum := by decide
  have hdescent : baseEnd_835585 < baseStart_835585 := by decide
  rcases family_descends (prefixWord ++ tailWord_835585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835630 : List Nat := [4, 1, 3, 1, 1, 2, 2, 1, 1, 6]
def baseStart_835630 : Nat := 118140960795 + 835630 * 2 ^ 59
def prefixEnd_835630 : Nat := 4983230072969 + 3 ^ 40 * 835630 * 2
def baseEnd_835630 : Nat := 286053226211113884988009

theorem tailTrace_835630 : CollatzResearch.WordTrace tailWord_835630 prefixEnd_835630 286053226211113884988009 := by
  unfold tailWord_835630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3809741245332837385881043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20318619975108466058032229 3809741245332837385881043)
  ·
    refine ⟨5714611867999256078821565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3809741245332837385881043 5714611867999256078821565)
    ·
      refine ⟨2142979450499721029558087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5714611867999256078821565 2142979450499721029558087)
      ·
        refine ⟨3214469175749581544337131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2142979450499721029558087 3214469175749581544337131)
        ·
          refine ⟨4821703763624372316505697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3214469175749581544337131 4821703763624372316505697)
          ·
            refine ⟨3616277822718279237379273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4821703763624372316505697 3616277822718279237379273)
            ·
              refine ⟨2712208367038709428034455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3616277822718279237379273 2712208367038709428034455)
              ·
                refine ⟨4068312550558064142051683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2712208367038709428034455 4068312550558064142051683)
                ·
                  refine ⟨6102468825837096213077525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4068312550558064142051683 6102468825837096213077525)
                  ·
                    refine ⟨286053226211113884988009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6102468825837096213077525 286053226211113884988009)
                    ·
                      rfl

theorem cell22_835630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_835630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_835630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_835630 prefixEnd_835630 := by exact prefixLift 835630
  have htrace : WordTrace (prefixWord ++ tailWord_835630) baseStart_835630 baseEnd_835630 := by
    simpa [prefixWord, tailWord_835630, baseEnd_835630] using wordTrace_append hprefix tailTrace_835630
  have hstable : (prefixWord ++ tailWord_835630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835630).length < 2 ^ (prefixWord ++ tailWord_835630).sum := by decide
  have hdescent : baseEnd_835630 < baseStart_835630 := by decide
  rcases family_descends (prefixWord ++ tailWord_835630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835658 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 2, 6]
def baseStart_835658 : Nat := 118140960795 + 835658 * 2 ^ 59
def prefixEnd_835658 : Nat := 4983230072969 + 3 ^ 40 * 835658 * 2
def baseEnd_835658 : Nat := 286062811183331145287923

theorem tailTrace_835658 : CollatzResearch.WordTrace tailWord_835658 prefixEnd_835658 286062811183331145287923 := by
  unfold tailWord_835658
  simp only [CollatzResearch.WordTrace]
  refine ⟨7619737801640314967266907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20319300804374173246045085 7619737801640314967266907)
  ·
    refine ⟨11429606702460472450900361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7619737801640314967266907 11429606702460472450900361)
    ·
      refine ⟨8572205026845354338175271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11429606702460472450900361 8572205026845354338175271)
      ·
        refine ⟨12858307540268031507262907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8572205026845354338175271 12858307540268031507262907)
        ·
          refine ⟨19287461310402047260894361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12858307540268031507262907 19287461310402047260894361)
          ·
            refine ⟨14465595982801535445670771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19287461310402047260894361 14465595982801535445670771)
            ·
              refine ⟨21698393974202303168506157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14465595982801535445670771 21698393974202303168506157)
              ·
                refine ⟨8136897740325863688189809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21698393974202303168506157 8136897740325863688189809)
                ·
                  refine ⟨6102673305244397766142357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8136897740325863688189809 6102673305244397766142357)
                  ·
                    refine ⟨286062811183331145287923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6102673305244397766142357 286062811183331145287923)
                    ·
                      rfl

theorem cell22_835658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_835658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_835658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_835658 prefixEnd_835658 := by exact prefixLift 835658
  have htrace : WordTrace (prefixWord ++ tailWord_835658) baseStart_835658 baseEnd_835658 := by
    simpa [prefixWord, tailWord_835658, baseEnd_835658] using wordTrace_append hprefix tailTrace_835658
  have hstable : (prefixWord ++ tailWord_835658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835658).length < 2 ^ (prefixWord ++ tailWord_835658).sum := by decide
  have hdescent : baseEnd_835658 < baseStart_835658 := by decide
  rcases family_descends (prefixWord ++ tailWord_835658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835666 : List Nat := [3, 2, 2, 1, 4, 2, 2, 1, 2, 3]
def baseStart_835666 : Nat := 118140960795 + 835666 * 2 ^ 59
def prefixEnd_835666 : Nat := 4983230072969 + 3 ^ 40 * 835666 * 2
def baseEnd_835666 : Nat := 286065549746821791087899

theorem tailTrace_835666 : CollatzResearch.WordTrace tailWord_835666 prefixEnd_835666 286065549746821791087899 := by
  unfold tailWord_835666
  simp only [CollatzResearch.WordTrace]
  refine ⟨7619810747633069308839713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20319495327021518156905901 7619810747633069308839713)
  ·
    refine ⟨5714858060724801981629785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7619810747633069308839713 5714858060724801981629785)
    ·
      refine ⟨4286143545543601486222339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5714858060724801981629785 4286143545543601486222339)
      ·
        refine ⟨6429215318315402229333509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4286143545543601486222339 6429215318315402229333509)
        ·
          refine ⟨1205477872184137918000033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6429215318315402229333509 1205477872184137918000033)
          ·
            refine ⟨904108404138103438500025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1205477872184137918000033 904108404138103438500025)
            ·
              refine ⟨678081303103577578875019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 904108404138103438500025 678081303103577578875019)
              ·
                refine ⟨1017121954655366368312529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 678081303103577578875019 1017121954655366368312529)
                ·
                  refine ⟨762841465991524776234397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1017121954655366368312529 762841465991524776234397)
                  ·
                    refine ⟨286065549746821791087899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 762841465991524776234397 286065549746821791087899)
                    ·
                      rfl

theorem cell22_835666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_835666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_835666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_835666 prefixEnd_835666 := by exact prefixLift 835666
  have htrace : WordTrace (prefixWord ++ tailWord_835666) baseStart_835666 baseEnd_835666 := by
    simpa [prefixWord, tailWord_835666, baseEnd_835666] using wordTrace_append hprefix tailTrace_835666
  have hstable : (prefixWord ++ tailWord_835666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835666).length < 2 ^ (prefixWord ++ tailWord_835666).sum := by decide
  have hdescent : baseEnd_835666 < baseStart_835666 := by decide
  rcases family_descends (prefixWord ++ tailWord_835666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835694 : List Nat := [4, 1, 2, 2, 1, 1, 2, 5, 1, 3]
def baseStart_835694 : Nat := 118140960795 + 835694 * 2 ^ 59
def prefixEnd_835694 : Nat := 4983230072969 + 3 ^ 40 * 835694 * 2
def baseEnd_835694 : Nat := 286075134719039051387813

theorem tailTrace_835694 : CollatzResearch.WordTrace tailWord_835694 prefixEnd_835694 286075134719039051387813 := by
  unfold tailWord_835694
  simp only [CollatzResearch.WordTrace]
  refine ⟨3810033029303854752172267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20320176156287225344918757 3810033029303854752172267)
  ·
    refine ⟨5715049543955782128258401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3810033029303854752172267 5715049543955782128258401)
    ·
      refine ⟨4286287157966836596193801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5715049543955782128258401 4286287157966836596193801)
      ·
        refine ⟨3214715368475127447145351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4286287157966836596193801 3214715368475127447145351)
        ·
          refine ⟨4822073052712691170718027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3214715368475127447145351 4822073052712691170718027)
          ·
            refine ⟨7233109579069036756077041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4822073052712691170718027 7233109579069036756077041)
            ·
              refine ⟨5424832184301777567057781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7233109579069036756077041 5424832184301777567057781)
              ·
                refine ⟨508578017278291646911667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5424832184301777567057781 508578017278291646911667)
                ·
                  refine ⟨762867025917437470367501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 508578017278291646911667 762867025917437470367501)
                  ·
                    refine ⟨286075134719039051387813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 762867025917437470367501 286075134719039051387813)
                    ·
                      rfl

theorem cell22_835694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_835694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_835694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_835694 prefixEnd_835694 := by exact prefixLift 835694
  have htrace : WordTrace (prefixWord ++ tailWord_835694) baseStart_835694 baseEnd_835694 := by
    simpa [prefixWord, tailWord_835694, baseEnd_835694] using wordTrace_append hprefix tailTrace_835694
  have hstable : (prefixWord ++ tailWord_835694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835694).length < 2 ^ (prefixWord ++ tailWord_835694).sum := by decide
  have hdescent : baseEnd_835694 < baseStart_835694 := by decide
  rcases family_descends (prefixWord ++ tailWord_835694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835758 : List Nat := [4, 1, 4, 2, 2, 1, 1, 2, 5]
def baseStart_835758 : Nat := 118140960795 + 835758 * 2 ^ 59
def prefixEnd_835758 : Nat := 4983230072969 + 3 ^ 40 * 835758 * 2
def baseEnd_835758 : Nat := 95365681075654739262539

theorem tailTrace_835758 : CollatzResearch.WordTrace tailWord_835758 prefixEnd_835758 95365681075654739262539 := by
  unfold tailWord_835758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3810324813274872118463491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20321732337465984631805285 3810324813274872118463491)
  ·
    refine ⟨5715487219912308177695237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3810324813274872118463491 5715487219912308177695237)
    ·
      refine ⟨1071653853733557783317857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5715487219912308177695237 1071653853733557783317857)
      ·
        refine ⟨803740390300168337488393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1071653853733557783317857 803740390300168337488393)
        ·
          refine ⟨602805292725126253116295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 803740390300168337488393 602805292725126253116295)
          ·
            refine ⟨904207939087689379674443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602805292725126253116295 904207939087689379674443)
            ·
              refine ⟨1356311908631534069511665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 904207939087689379674443 1356311908631534069511665)
              ·
                refine ⟨1017233931473650552133749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1356311908631534069511665 1017233931473650552133749)
                ·
                  refine ⟨95365681075654739262539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1017233931473650552133749 95365681075654739262539)
                  ·
                    rfl

theorem cell22_835758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_835758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_835758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_835758 prefixEnd_835758 := by exact prefixLift 835758
  have htrace : WordTrace (prefixWord ++ tailWord_835758) baseStart_835758 baseEnd_835758 := by
    simpa [prefixWord, tailWord_835758, baseEnd_835758] using wordTrace_append hprefix tailTrace_835758
  have hstable : (prefixWord ++ tailWord_835758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835758).length < 2 ^ (prefixWord ++ tailWord_835758).sum := by decide
  have hdescent : baseEnd_835758 < baseStart_835758 := by decide
  rcases family_descends (prefixWord ++ tailWord_835758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835767 : List Nat := [1, 1, 3, 1, 4, 3, 1, 1, 4, 3]
def baseStart_835767 : Nat := 118140960795 + 835767 * 2 ^ 59
def prefixEnd_835767 : Nat := 4983230072969 + 3 ^ 40 * 835767 * 2
def baseEnd_835767 : Nat := 286100124110891194312589

theorem tailTrace_835767 : CollatzResearch.WordTrace tailWord_835767 prefixEnd_835767 286100124110891194312589 := by
  unfold tailWord_835767
  simp only [CollatzResearch.WordTrace]
  refine ⟨30482926763166371484785555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20321951175444247656523703 30482926763166371484785555)
  ·
    refine ⟨45724390144749557227178333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30482926763166371484785555 45724390144749557227178333)
    ·
      refine ⟨17146646304281083960191875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45724390144749557227178333 17146646304281083960191875)
      ·
        refine ⟨25719969456421625940287813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17146646304281083960191875 25719969456421625940287813)
        ·
          refine ⟨4822494273079054863803965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25719969456421625940287813 4822494273079054863803965)
          ·
            refine ⟨1808435352404645573926487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4822494273079054863803965 1808435352404645573926487)
            ·
              refine ⟨2712653028606968360889731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1808435352404645573926487 2712653028606968360889731)
              ·
                refine ⟨4068979542910452541334597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2712653028606968360889731 4068979542910452541334597)
                ·
                  refine ⟨762933664295709851500237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4068979542910452541334597 762933664295709851500237)
                  ·
                    refine ⟨286100124110891194312589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 762933664295709851500237 286100124110891194312589)
                    ·
                      rfl

theorem cell22_835767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4, 3].length) (baseStart_835767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_835767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_835767 prefixEnd_835767 := by exact prefixLift 835767
  have htrace : WordTrace (prefixWord ++ tailWord_835767) baseStart_835767 baseEnd_835767 := by
    simpa [prefixWord, tailWord_835767, baseEnd_835767] using wordTrace_append hprefix tailTrace_835767
  have hstable : (prefixWord ++ tailWord_835767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835767).length < 2 ^ (prefixWord ++ tailWord_835767).sum := by decide
  have hdescent : baseEnd_835767 < baseStart_835767 := by decide
  rcases family_descends (prefixWord ++ tailWord_835767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835797 : List Nat := [1, 3, 2, 4, 2, 1, 1, 8]
def baseStart_835797 : Nat := 118140960795 + 835797 * 2 ^ 59
def prefixEnd_835797 : Nat := 4983230072969 + 3 ^ 40 * 835797 * 2
def baseEnd_835797 : Nat := 31790043747109012895833

theorem tailTrace_835797 : CollatzResearch.WordTrace tailWord_835797 prefixEnd_835797 31790043747109012895833 := by
  unfold tailWord_835797
  simp only [CollatzResearch.WordTrace]
  refine ⟨30484020953057686608377645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20322680635371791072251763 30484020953057686608377645)
  ·
    refine ⟨11431507857396632478141617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30484020953057686608377645 11431507857396632478141617)
    ·
      refine ⟨8573630893047474358606213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11431507857396632478141617 8573630893047474358606213)
      ·
        refine ⟨1607555792446401442238665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8573630893047474358606213 1607555792446401442238665)
        ·
          refine ⟨1205666844334801081678999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1607555792446401442238665 1205666844334801081678999)
          ·
            refine ⟨1808500266502201622518499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1205666844334801081678999 1808500266502201622518499)
            ·
              refine ⟨2712750399753302433777749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1808500266502201622518499 2712750399753302433777749)
              ·
                refine ⟨31790043747109012895833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2712750399753302433777749 31790043747109012895833)
                ·
                  rfl

theorem cell22_835797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 8].length) (baseStart_835797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_835797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_835797 prefixEnd_835797 := by exact prefixLift 835797
  have htrace : WordTrace (prefixWord ++ tailWord_835797) baseStart_835797 baseEnd_835797 := by
    simpa [prefixWord, tailWord_835797, baseEnd_835797] using wordTrace_append hprefix tailTrace_835797
  have hstable : (prefixWord ++ tailWord_835797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835797).length < 2 ^ (prefixWord ++ tailWord_835797).sum := by decide
  have hdescent : baseEnd_835797 < baseStart_835797 := by decide
  rcases family_descends (prefixWord ++ tailWord_835797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835825 : List Nat := [1, 2, 2, 2, 2, 1, 4, 1, 7]
def baseStart_835825 : Nat := 118140960795 + 835825 * 2 ^ 59
def prefixEnd_835825 : Nat := 4983230072969 + 3 ^ 40 * 835825 * 2
def baseEnd_835825 : Nat := 95373326232066125454137

theorem tailTrace_835825 : CollatzResearch.WordTrace tailWord_835825 prefixEnd_835825 95373326232066125454137 := by
  unfold tailWord_835825
  simp only [CollatzResearch.WordTrace]
  refine ⟨30485042196956247390396929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20323361464637498260264619 30485042196956247390396929)
  ·
    refine ⟨22863781647717185542797697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30485042196956247390396929 22863781647717185542797697)
    ·
      refine ⟨17147836235787889157098273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22863781647717185542797697 17147836235787889157098273)
      ·
        refine ⟨12860877176840916867823705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17147836235787889157098273 12860877176840916867823705)
        ·
          refine ⟨9645657882630687650867779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12860877176840916867823705 9645657882630687650867779)
          ·
            refine ⟨14468486823946031476301669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9645657882630687650867779 14468486823946031476301669)
            ·
              refine ⟨2712841279489880901806563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14468486823946031476301669 2712841279489880901806563)
              ·
                refine ⟨4069261919234821352709845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2712841279489880901806563 4069261919234821352709845)
                ·
                  refine ⟨95373326232066125454137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4069261919234821352709845 95373326232066125454137)
                  ·
                    rfl

theorem cell22_835825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 7].length) (baseStart_835825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_835825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_835825 prefixEnd_835825 := by exact prefixLift 835825
  have htrace : WordTrace (prefixWord ++ tailWord_835825) baseStart_835825 baseEnd_835825 := by
    simpa [prefixWord, tailWord_835825, baseEnd_835825] using wordTrace_append hprefix tailTrace_835825
  have hstable : (prefixWord ++ tailWord_835825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835825).length < 2 ^ (prefixWord ++ tailWord_835825).sum := by decide
  have hdescent : baseEnd_835825 < baseStart_835825 := by decide
  rcases family_descends (prefixWord ++ tailWord_835825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835840 : List Nat := [2, 1, 1, 2, 1, 1, 4, 3, 2, 5]
def baseStart_835840 : Nat := 118140960795 + 835840 * 2 ^ 59
def prefixEnd_835840 : Nat := 4983230072969 + 3 ^ 40 * 835840 * 2
def baseEnd_835840 : Nat := 286125113502743337237365

theorem tailTrace_835840 : CollatzResearch.WordTrace tailWord_835840 prefixEnd_835840 286125113502743337237365 := by
  unfold tailWord_835840
  simp only [CollatzResearch.WordTrace]
  refine ⟨15242794645950952476096487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20323726194601269968128649 15242794645950952476096487)
  ·
    refine ⟨22864191968926428714144731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15242794645950952476096487 22864191968926428714144731)
    ·
      refine ⟨34296287953389643071217097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22864191968926428714144731 34296287953389643071217097)
      ·
        refine ⟨25722215965042232303412823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34296287953389643071217097 25722215965042232303412823)
        ·
          refine ⟨38583323947563348455119235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25722215965042232303412823 38583323947563348455119235)
          ·
            refine ⟨57874985921345022682678853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38583323947563348455119235 57874985921345022682678853)
            ·
              refine ⟨10851559860252191753002285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57874985921345022682678853 10851559860252191753002285)
              ·
                refine ⟨4069334947594571907375857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10851559860252191753002285 4069334947594571907375857)
                ·
                  refine ⟨3052001210695928930531893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4069334947594571907375857 3052001210695928930531893)
                  ·
                    refine ⟨286125113502743337237365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3052001210695928930531893 286125113502743337237365)
                    ·
                      rfl

theorem cell22_835840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 5].length) (baseStart_835840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_835840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_835840 prefixEnd_835840 := by exact prefixLift 835840
  have htrace : WordTrace (prefixWord ++ tailWord_835840) baseStart_835840 baseEnd_835840 := by
    simpa [prefixWord, tailWord_835840, baseEnd_835840] using wordTrace_append hprefix tailTrace_835840
  have hstable : (prefixWord ++ tailWord_835840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835840).length < 2 ^ (prefixWord ++ tailWord_835840).sum := by decide
  have hdescent : baseEnd_835840 < baseStart_835840 := by decide
  rcases family_descends (prefixWord ++ tailWord_835840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835880 : List Nat := [2, 1, 5, 1, 3, 2, 2, 2, 1, 3]
def baseStart_835880 : Nat := 118140960795 + 835880 * 2 ^ 59
def prefixEnd_835880 : Nat := 4983230072969 + 3 ^ 40 * 835880 * 2
def baseEnd_835880 : Nat := 286138806320196566237243

theorem tailTrace_835880 : CollatzResearch.WordTrace tailWord_835880 prefixEnd_835880 286138806320196566237243 := by
  unfold tailWord_835880
  simp only [CollatzResearch.WordTrace]
  refine ⟨15243524105878495891824547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20324698807837994522432729 15243524105878495891824547)
  ·
    refine ⟨22865286158817743837736821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15243524105878495891824547 22865286158817743837736821)
    ·
      refine ⟨2143620577389163484787827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22865286158817743837736821 2143620577389163484787827)
      ·
        refine ⟨3215430866083745227181741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2143620577389163484787827 3215430866083745227181741)
        ·
          refine ⟨1205786574781404460193153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3215430866083745227181741 1205786574781404460193153)
          ·
            refine ⟨904339931086053345144865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1205786574781404460193153 904339931086053345144865)
            ·
              refine ⟨678254948314540008858649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 904339931086053345144865 678254948314540008858649)
              ·
                refine ⟨508691211235905006643987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 678254948314540008858649 508691211235905006643987)
                ·
                  refine ⟨763036816853857509965981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 508691211235905006643987 763036816853857509965981)
                  ·
                    refine ⟨286138806320196566237243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 763036816853857509965981 286138806320196566237243)
                    ·
                      rfl

theorem cell22_835880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_835880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_835880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_835880 prefixEnd_835880 := by exact prefixLift 835880
  have htrace : WordTrace (prefixWord ++ tailWord_835880) baseStart_835880 baseEnd_835880 := by
    simpa [prefixWord, tailWord_835880, baseEnd_835880] using wordTrace_append hprefix tailTrace_835880
  have hstable : (prefixWord ++ tailWord_835880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835880).length < 2 ^ (prefixWord ++ tailWord_835880).sum := by decide
  have hdescent : baseEnd_835880 < baseStart_835880 := by decide
  rcases family_descends (prefixWord ++ tailWord_835880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835947 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 7, 3]
def baseStart_835947 : Nat := 118140960795 + 835947 * 2 ^ 59
def prefixEnd_835947 : Nat := 4983230072969 + 3 ^ 40 * 835947 * 2
def baseEnd_835947 : Nat := 286161741789430724812037

theorem tailTrace_835947 : CollatzResearch.WordTrace tailWord_835947 prefixEnd_835947 286161741789430724812037 := by
  unfold tailWord_835947
  simp only [CollatzResearch.WordTrace]
  refine ⟨30489491902514262226338095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20326327935009508150892063 30489491902514262226338095)
  ·
    refine ⟨45734237853771393339507143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30489491902514262226338095 45734237853771393339507143)
    ·
      refine ⟨68601356780657090009260715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45734237853771393339507143 68601356780657090009260715)
      ·
        refine ⟨102902035170985635013891073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68601356780657090009260715 102902035170985635013891073)
        ·
          refine ⟨77176526378239226260418305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102902035170985635013891073 77176526378239226260418305)
          ·
            refine ⟨57882394783679419695313729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77176526378239226260418305 57882394783679419695313729)
            ·
              refine ⟨43411796087759564771485297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57882394783679419695313729 43411796087759564771485297)
              ·
                refine ⟨32558847065819673578613973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43411796087759564771485297 32558847065819673578613973)
                ·
                  refine ⟨763097978105148599498765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 32558847065819673578613973 763097978105148599498765)
                  ·
                    refine ⟨286161741789430724812037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 763097978105148599498765 286161741789430724812037)
                    ·
                      rfl

theorem cell22_835947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7, 3].length) (baseStart_835947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_835947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_835947 prefixEnd_835947 := by exact prefixLift 835947
  have htrace : WordTrace (prefixWord ++ tailWord_835947) baseStart_835947 baseEnd_835947 := by
    simpa [prefixWord, tailWord_835947, baseEnd_835947] using wordTrace_append hprefix tailTrace_835947
  have hstable : (prefixWord ++ tailWord_835947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835947).length < 2 ^ (prefixWord ++ tailWord_835947).sum := by decide
  have hdescent : baseEnd_835947 < baseStart_835947 := by decide
  rcases family_descends (prefixWord ++ tailWord_835947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835977 : List Nat := [1, 2, 1, 1, 6, 1, 1, 2, 7]
def baseStart_835977 : Nat := 118140960795 + 835977 * 2 ^ 59
def prefixEnd_835977 : Nat := 4983230072969 + 3 ^ 40 * 835977 * 2
def baseEnd_835977 : Nat := 95390670467506882187315

theorem tailTrace_835977 : CollatzResearch.WordTrace tailWord_835977 prefixEnd_835977 95390670467506882187315 := by
  unfold tailWord_835977
  simp only [CollatzResearch.WordTrace]
  refine ⟨30490586092405577349930185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20327057394937051566620123 30490586092405577349930185)
  ·
    refine ⟨22867939569304183012447639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30490586092405577349930185 22867939569304183012447639)
    ·
      refine ⟨34301909353956274518671459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22867939569304183012447639 34301909353956274518671459)
      ·
        refine ⟨51452864030934411778007189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34301909353956274518671459 51452864030934411778007189)
        ·
          refine ⟨2411853001450050552094087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51452864030934411778007189 2411853001450050552094087)
          ·
            refine ⟨3617779502175075828141131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2411853001450050552094087 3617779502175075828141131)
            ·
              refine ⟨5426669253262613742211697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3617779502175075828141131 5426669253262613742211697)
              ·
                refine ⟨4070001939946960306658773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5426669253262613742211697 4070001939946960306658773)
                ·
                  refine ⟨95390670467506882187315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4070001939946960306658773 95390670467506882187315)
                  ·
                    rfl

theorem cell22_835977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 7].length) (baseStart_835977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_835977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_835977 prefixEnd_835977 := by exact prefixLift 835977
  have htrace : WordTrace (prefixWord ++ tailWord_835977) baseStart_835977 baseEnd_835977 := by
    simpa [prefixWord, tailWord_835977, baseEnd_835977] using wordTrace_append hprefix tailTrace_835977
  have hstable : (prefixWord ++ tailWord_835977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835977).length < 2 ^ (prefixWord ++ tailWord_835977).sum := by decide
  have hdescent : baseEnd_835977 < baseStart_835977 := by decide
  rcases family_descends (prefixWord ++ tailWord_835977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835998 : List Nat := [4, 3, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_835998 : Nat := 118140960795 + 835998 * 2 ^ 59
def prefixEnd_835998 : Nat := 4983230072969 + 3 ^ 40 * 835998 * 2
def baseEnd_835998 : Nat := 286179200131683591786881

theorem tailTrace_835998 : CollatzResearch.WordTrace tailWord_835998 prefixEnd_835998 286179200131683591786881 := by
  unfold tailWord_835998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3811419003166187242055581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20327568016886331957629765 3811419003166187242055581)
  ·
    refine ⟨1429282126187320215770843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3811419003166187242055581 1429282126187320215770843)
    ·
      refine ⟨2143923189280980323656265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1429282126187320215770843 2143923189280980323656265)
      ·
        refine ⟨1607942391960735242742199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2143923189280980323656265 1607942391960735242742199)
        ·
          refine ⟨2411913587941102864113299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1607942391960735242742199 2411913587941102864113299)
          ·
            refine ⟨3617870381911654296169949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2411913587941102864113299 3617870381911654296169949)
            ·
              refine ⟨1356701393216870361063731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3617870381911654296169949 1356701393216870361063731)
              ·
                refine ⟨2035052089825305541595597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1356701393216870361063731 2035052089825305541595597)
                ·
                  refine ⟨763144533684489578098349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2035052089825305541595597 763144533684489578098349)
                  ·
                    refine ⟨286179200131683591786881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 763144533684489578098349 286179200131683591786881)
                    ·
                      rfl

theorem cell22_835998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_835998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_835998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_835998 prefixEnd_835998 := by exact prefixLift 835998
  have htrace : WordTrace (prefixWord ++ tailWord_835998) baseStart_835998 baseEnd_835998 := by
    simpa [prefixWord, tailWord_835998, baseEnd_835998] using wordTrace_append hprefix tailTrace_835998
  have hstable : (prefixWord ++ tailWord_835998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835998).length < 2 ^ (prefixWord ++ tailWord_835998).sum := by decide
  have hdescent : baseEnd_835998 < baseStart_835998 := by decide
  rcases family_descends (prefixWord ++ tailWord_835998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836071 : List Nat := [1, 1, 5, 2, 1, 1, 1, 5, 2, 3]
def baseStart_836071 : Nat := 118140960795 + 836071 * 2 ^ 59
def prefixEnd_836071 : Nat := 4983230072969 + 3 ^ 40 * 836071 * 2
def baseEnd_836071 : Nat := 286204189523535734711657

theorem tailTrace_836071 : CollatzResearch.WordTrace tailWord_836071 prefixEnd_836071 286204189523535734711657 := by
  unfold tailWord_836071
  simp only [CollatzResearch.WordTrace]
  refine ⟨30494014554065031403852067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20329343036043354269234711 30494014554065031403852067)
  ·
    refine ⟨45741021831097547105778101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30494014554065031403852067 45741021831097547105778101)
    ·
      refine ⟨4288220796665395041166697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45741021831097547105778101 4288220796665395041166697)
      ·
        refine ⟨3216165597499046280875023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4288220796665395041166697 3216165597499046280875023)
        ·
          refine ⟨4824248396248569421312535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3216165597499046280875023 4824248396248569421312535)
          ·
            refine ⟨7236372594372854131968803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4824248396248569421312535 7236372594372854131968803)
            ·
              refine ⟨10854558891559281197953205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7236372594372854131968803 10854558891559281197953205)
              ·
                refine ⟨1017614896083682612308113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10854558891559281197953205 1017614896083682612308113)
                ·
                  refine ⟨763211172062761959231085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1017614896083682612308113 763211172062761959231085)
                  ·
                    refine ⟨286204189523535734711657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 763211172062761959231085 286204189523535734711657)
                    ·
                      rfl

theorem cell22_836071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_836071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836071 prefixEnd_836071 := by exact prefixLift 836071
  have htrace : WordTrace (prefixWord ++ tailWord_836071) baseStart_836071 baseEnd_836071 := by
    simpa [prefixWord, tailWord_836071, baseEnd_836071] using wordTrace_append hprefix tailTrace_836071
  have hstable : (prefixWord ++ tailWord_836071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836071).length < 2 ^ (prefixWord ++ tailWord_836071).sum := by decide
  have hdescent : baseEnd_836071 < baseStart_836071 := by decide
  rcases family_descends (prefixWord ++ tailWord_836071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836099 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 5, 3]
def baseStart_836099 : Nat := 118140960795 + 836099 * 2 ^ 59
def prefixEnd_836099 : Nat := 4983230072969 + 3 ^ 40 * 836099 * 2
def baseEnd_836099 : Nat := 286213774495752995011571

theorem tailTrace_836099 : CollatzResearch.WordTrace tailWord_836099 prefixEnd_836099 286213774495752995011571 := by
  unfold tailWord_836099
  simp only [CollatzResearch.WordTrace]
  refine ⟨30495035797963592185871351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20330023865309061457247567 30495035797963592185871351)
  ·
    refine ⟨45742553696945388278807027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30495035797963592185871351 45742553696945388278807027)
    ·
      refine ⟨68613830545418082418210541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45742553696945388278807027 68613830545418082418210541)
      ·
        refine ⟨25730186454531780906828953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68613830545418082418210541 25730186454531780906828953)
        ·
          refine ⟨19297639840898835680121715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25730186454531780906828953 19297639840898835680121715)
          ·
            refine ⟨28946459761348253520182573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19297639840898835680121715 28946459761348253520182573)
            ·
              refine ⟨10854922410505595070068465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28946459761348253520182573 10854922410505595070068465)
              ·
                refine ⟨8141191807879196302551349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10854922410505595070068465 8141191807879196302551349)
                ·
                  refine ⟨763236731988674653364189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8141191807879196302551349 763236731988674653364189)
                  ·
                    refine ⟨286213774495752995011571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 763236731988674653364189 286213774495752995011571)
                    ·
                      rfl

theorem cell22_836099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5, 3].length) (baseStart_836099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836099 prefixEnd_836099 := by exact prefixLift 836099
  have htrace : WordTrace (prefixWord ++ tailWord_836099) baseStart_836099 baseEnd_836099 := by
    simpa [prefixWord, tailWord_836099, baseEnd_836099] using wordTrace_append hprefix tailTrace_836099
  have hstable : (prefixWord ++ tailWord_836099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836099).length < 2 ^ (prefixWord ++ tailWord_836099).sum := by decide
  have hdescent : baseEnd_836099 < baseStart_836099 := by decide
  rcases family_descends (prefixWord ++ tailWord_836099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836135 : List Nat := [1, 1, 7, 2, 1, 2, 2, 6]
def baseStart_836135 : Nat := 118140960795 + 836135 * 2 ^ 59
def prefixEnd_836135 : Nat := 4983230072969 + 3 ^ 40 * 836135 * 2
def baseEnd_836135 : Nat := 31802899781273433456829

theorem tailTrace_836135 : CollatzResearch.WordTrace tailWord_836135 prefixEnd_836135 31802899781273433456829 := by
  unfold tailWord_836135
  simp only [CollatzResearch.WordTrace]
  refine ⟨30496348825833170334181859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20330899217222113556121239 30496348825833170334181859)
  ·
    refine ⟨45744523238749755501272789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30496348825833170334181859 45744523238749755501272789)
    ·
      refine ⟨1072137263408197394561081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 45744523238749755501272789 1072137263408197394561081)
      ·
        refine ⟨804102947556148045920811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1072137263408197394561081 804102947556148045920811)
        ·
          refine ⟨1206154421334222068881217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 804102947556148045920811 1206154421334222068881217)
          ·
            refine ⟨904615816000666551660913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1206154421334222068881217 904615816000666551660913)
            ·
              refine ⟨678461862000499913745685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 904615816000666551660913 678461862000499913745685)
              ·
                refine ⟨31802899781273433456829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 678461862000499913745685 31802899781273433456829)
                ·
                  rfl

theorem cell22_836135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 6].length) (baseStart_836135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836135 prefixEnd_836135 := by exact prefixLift 836135
  have htrace : WordTrace (prefixWord ++ tailWord_836135) baseStart_836135 baseEnd_836135 := by
    simpa [prefixWord, tailWord_836135, baseEnd_836135] using wordTrace_append hprefix tailTrace_836135
  have hstable : (prefixWord ++ tailWord_836135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836135).length < 2 ^ (prefixWord ++ tailWord_836135).sum := by decide
  have hdescent : baseEnd_836135 < baseStart_836135 := by decide
  rcases family_descends (prefixWord ++ tailWord_836135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836193 : List Nat := [1, 2, 3, 1, 1, 6, 1, 2, 1, 4]
def baseStart_836193 : Nat := 118140960795 + 836193 * 2 ^ 59
def prefixEnd_836193 : Nat := 4983230072969 + 3 ^ 40 * 836193 * 2
def baseEnd_836193 : Nat := 286245952616768083161283

theorem tailTrace_836193 : CollatzResearch.WordTrace tailWord_836193 prefixEnd_836193 286245952616768083161283 := by
  unfold tailWord_836193
  simp only [CollatzResearch.WordTrace]
  refine ⟨30498464259623046239793233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20332309506415364159862155 30498464259623046239793233)
  ·
    refine ⟨22873848194717284679844925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30498464259623046239793233 22873848194717284679844925)
    ·
      refine ⟨8577693073018981754941847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22873848194717284679844925 8577693073018981754941847)
      ·
        refine ⟨12866539609528472632412771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8577693073018981754941847 12866539609528472632412771)
        ·
          refine ⟨19299809414292708948619157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12866539609528472632412771 19299809414292708948619157)
          ·
            refine ⟨904678566294970731966523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19299809414292708948619157 904678566294970731966523)
            ·
              refine ⟨1357017849442456097949785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 904678566294970731966523 1357017849442456097949785)
              ·
                refine ⟨1017763387081842073462339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1357017849442456097949785 1017763387081842073462339)
                ·
                  refine ⟨1526645080622763110193509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1017763387081842073462339 1526645080622763110193509)
                  ·
                    refine ⟨286245952616768083161283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1526645080622763110193509 286245952616768083161283)
                    ·
                      rfl

theorem cell22_836193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_836193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836193 prefixEnd_836193 := by exact prefixLift 836193
  have htrace : WordTrace (prefixWord ++ tailWord_836193) baseStart_836193 baseEnd_836193 := by
    simpa [prefixWord, tailWord_836193, baseEnd_836193] using wordTrace_append hprefix tailTrace_836193
  have hstable : (prefixWord ++ tailWord_836193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836193).length < 2 ^ (prefixWord ++ tailWord_836193).sum := by decide
  have hdescent : baseEnd_836193 < baseStart_836193 := by decide
  rcases family_descends (prefixWord ++ tailWord_836193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836204 : List Nat := [2, 2, 1, 1, 3, 1, 2, 3, 1, 6]
def baseStart_836204 : Nat := 118140960795 + 836204 * 2 ^ 59
def prefixEnd_836204 : Nat := 4983230072969 + 3 ^ 40 * 836204 * 2
def baseEnd_836204 : Nat := 286249718141567721136249

theorem tailTrace_836204 : CollatzResearch.WordTrace tailWord_836204 prefixEnd_836204 286249718141567721136249 := by
  unfold tailWord_836204
  simp only [CollatzResearch.WordTrace]
  refine ⟨15249432731291597559221833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20332576975055463412295777 15249432731291597559221833)
  ·
    refine ⟨11437074548468698169416375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15249432731291597559221833 11437074548468698169416375)
    ·
      refine ⟨17155611822703047254124563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11437074548468698169416375 17155611822703047254124563)
      ·
        refine ⟨25733417734054570881186845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17155611822703047254124563 25733417734054570881186845)
        ·
          refine ⟨9650031650270464080445067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25733417734054570881186845 9650031650270464080445067)
          ·
            refine ⟨14475047475405696120667601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9650031650270464080445067 14475047475405696120667601)
            ·
              refine ⟨10856285606554272090500701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14475047475405696120667601 10856285606554272090500701)
              ·
                refine ⟨4071107102457852033937763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10856285606554272090500701 4071107102457852033937763)
                ·
                  refine ⟨6106660653686778050906645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4071107102457852033937763 6106660653686778050906645)
                  ·
                    refine ⟨286249718141567721136249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6106660653686778050906645 286249718141567721136249)
                    ·
                      rfl

theorem cell22_836204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_836204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836204 prefixEnd_836204 := by exact prefixLift 836204
  have htrace : WordTrace (prefixWord ++ tailWord_836204) baseStart_836204 baseEnd_836204 := by
    simpa [prefixWord, tailWord_836204, baseEnd_836204] using wordTrace_append hprefix tailTrace_836204
  have hstable : (prefixWord ++ tailWord_836204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836204).length < 2 ^ (prefixWord ++ tailWord_836204).sum := by decide
  have hdescent : baseEnd_836204 < baseStart_836204 := by decide
  rcases family_descends (prefixWord ++ tailWord_836204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836206 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 3, 5]
def baseStart_836206 : Nat := 118140960795 + 836206 * 2 ^ 59
def prefixEnd_836206 : Nat := 4983230072969 + 3 ^ 40 * 836206 * 2
def baseEnd_836206 : Nat := 286250402782440382586243

theorem tailTrace_836206 : CollatzResearch.WordTrace tailWord_836206 prefixEnd_836206 286250402782440382586243 := by
  unfold tailWord_836206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3812367301071993682502059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20332625605717299640010981 3812367301071993682502059)
  ·
    refine ⟨5718550951607990523753089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3812367301071993682502059 5718550951607990523753089)
    ·
      refine ⟨4288913213705992892814817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5718550951607990523753089 4288913213705992892814817)
      ·
        refine ⟨3216684910279494669611113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4288913213705992892814817 3216684910279494669611113)
        ·
          refine ⟨2412513682709621002208335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3216684910279494669611113 2412513682709621002208335)
          ·
            refine ⟨3618770524064431503312503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2412513682709621002208335 3618770524064431503312503)
            ·
              refine ⟨5428155786096647254968755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3618770524064431503312503 5428155786096647254968755)
              ·
                refine ⟨8142233679144970882453133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5428155786096647254968755 8142233679144970882453133)
                ·
                  refine ⟨3053337629679364080919925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8142233679144970882453133 3053337629679364080919925)
                  ·
                    refine ⟨286250402782440382586243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3053337629679364080919925 286250402782440382586243)
                    ·
                      rfl

theorem cell22_836206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_836206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836206 prefixEnd_836206 := by exact prefixLift 836206
  have htrace : WordTrace (prefixWord ++ tailWord_836206) baseStart_836206 baseEnd_836206 := by
    simpa [prefixWord, tailWord_836206, baseEnd_836206] using wordTrace_append hprefix tailTrace_836206
  have hstable : (prefixWord ++ tailWord_836206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836206).length < 2 ^ (prefixWord ++ tailWord_836206).sum := by decide
  have hdescent : baseEnd_836206 < baseStart_836206 := by decide
  rcases family_descends (prefixWord ++ tailWord_836206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836210 : List Nat := [3, 2, 1, 2, 4, 1, 3, 1, 1, 4]
def baseStart_836210 : Nat := 118140960795 + 836210 * 2 ^ 59
def prefixEnd_836210 : Nat := 4983230072969 + 3 ^ 40 * 836210 * 2
def baseEnd_836210 : Nat := 286251772064185705486231

theorem tailTrace_836210 : CollatzResearch.WordTrace tailWord_836210 prefixEnd_836210 286251772064185705486231 := by
  unfold tailWord_836210
  simp only [CollatzResearch.WordTrace]
  refine ⟨7624771075140364535790521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20332722867040972095441389 7624771075140364535790521)
  ·
    refine ⟨5718578306355273401842891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7624771075140364535790521 5718578306355273401842891)
    ·
      refine ⟨8577867459532910102764337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5718578306355273401842891 8577867459532910102764337)
      ·
        refine ⟨6433400594649682577073253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8577867459532910102764337 6433400594649682577073253)
        ·
          refine ⟨1206262611496815483201235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6433400594649682577073253 1206262611496815483201235)
          ·
            refine ⟨1809393917245223224801853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1206262611496815483201235 1809393917245223224801853)
            ·
              refine ⟨678522718966958709300695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1809393917245223224801853 678522718966958709300695)
              ·
                refine ⟨1017784078450438063951043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 678522718966958709300695 1017784078450438063951043)
                ·
                  refine ⟨1526676117675657095926565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1017784078450438063951043 1526676117675657095926565)
                  ·
                    refine ⟨286251772064185705486231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1526676117675657095926565 286251772064185705486231)
                    ·
                      rfl

theorem cell22_836210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_836210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836210 prefixEnd_836210 := by exact prefixLift 836210
  have htrace : WordTrace (prefixWord ++ tailWord_836210) baseStart_836210 baseEnd_836210 := by
    simpa [prefixWord, tailWord_836210, baseEnd_836210] using wordTrace_append hprefix tailTrace_836210
  have hstable : (prefixWord ++ tailWord_836210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836210).length < 2 ^ (prefixWord ++ tailWord_836210).sum := by decide
  have hdescent : baseEnd_836210 < baseStart_836210 := by decide
  rcases family_descends (prefixWord ++ tailWord_836210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836249 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 2, 6]
def baseStart_836249 : Nat := 118140960795 + 836249 * 2 ^ 59
def prefixEnd_836249 : Nat := 4983230072969 + 3 ^ 40 * 836249 * 2
def baseEnd_836249 : Nat := 286265122561202603761111

theorem tailTrace_836249 : CollatzResearch.WordTrace tailWord_836249 prefixEnd_836249 286265122561202603761111 := by
  unfold tailWord_836249
  simp only [CollatzResearch.WordTrace]
  refine ⟨30500506747420167803831801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20333671164946778535887867 30500506747420167803831801)
  ·
    refine ⟨22875380060565125852873851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30500506747420167803831801 22875380060565125852873851)
    ·
      refine ⟨34313070090847688779310777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22875380060565125852873851 34313070090847688779310777)
      ·
        refine ⟨25734802568135766584483083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34313070090847688779310777 25734802568135766584483083)
        ·
          refine ⟨38602203852203649876724625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25734802568135766584483083 38602203852203649876724625)
          ·
            refine ⟨28951652889152737407543469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38602203852203649876724625 28951652889152737407543469)
            ·
              refine ⟨10856869833432276527828801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28951652889152737407543469 10856869833432276527828801)
              ·
                refine ⟨8142652375074207395871601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10856869833432276527828801 8142652375074207395871601)
                ·
                  refine ⟨6106989281305655546903701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8142652375074207395871601 6106989281305655546903701)
                  ·
                    refine ⟨286265122561202603761111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6106989281305655546903701 286265122561202603761111)
                    ·
                      rfl

theorem cell22_836249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 6].length) (baseStart_836249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836249 prefixEnd_836249 := by exact prefixLift 836249
  have htrace : WordTrace (prefixWord ++ tailWord_836249) baseStart_836249 baseEnd_836249 := by
    simpa [prefixWord, tailWord_836249, baseEnd_836249] using wordTrace_append hprefix tailTrace_836249
  have hstable : (prefixWord ++ tailWord_836249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836249).length < 2 ^ (prefixWord ++ tailWord_836249).sum := by decide
  have hdescent : baseEnd_836249 < baseStart_836249 := by decide
  rcases family_descends (prefixWord ++ tailWord_836249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836285 : List Nat := [1, 4, 1, 2, 1, 3, 2, 4, 1, 3]
def baseStart_836285 : Nat := 118140960795 + 836285 * 2 ^ 59
def prefixEnd_836285 : Nat := 4983230072969 + 3 ^ 40 * 836285 * 2
def baseEnd_836285 : Nat := 286277446096910509861001

theorem tailTrace_836285 : CollatzResearch.WordTrace tailWord_836285 prefixEnd_836285 286277446096910509861001 := by
  unfold tailWord_836285
  simp only [CollatzResearch.WordTrace]
  refine ⟨30501819775289745952142309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20334546516859830634761539 30501819775289745952142309)
  ·
    refine ⟨5719091207866827366026683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30501819775289745952142309 5719091207866827366026683)
    ·
      refine ⟨8578636811800241049040025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5719091207866827366026683 8578636811800241049040025)
      ·
        refine ⟨6433977608850180786780019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8578636811800241049040025 6433977608850180786780019)
        ·
          refine ⟨9650966413275271180170029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6433977608850180786780019 9650966413275271180170029)
          ·
            refine ⟨3619112404978226692563761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9650966413275271180170029 3619112404978226692563761)
            ·
              refine ⟨2714334303733670019422821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3619112404978226692563761 2714334303733670019422821)
              ·
                refine ⟨508937681950063128641779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2714334303733670019422821 508937681950063128641779)
                ·
                  refine ⟨763406522925094692962669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 508937681950063128641779 763406522925094692962669)
                  ·
                    refine ⟨286277446096910509861001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 763406522925094692962669 286277446096910509861001)
                    ·
                      rfl

theorem cell22_836285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_836285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836285 prefixEnd_836285 := by exact prefixLift 836285
  have htrace : WordTrace (prefixWord ++ tailWord_836285) baseStart_836285 baseEnd_836285 := by
    simpa [prefixWord, tailWord_836285, baseEnd_836285] using wordTrace_append hprefix tailTrace_836285
  have hstable : (prefixWord ++ tailWord_836285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836285).length < 2 ^ (prefixWord ++ tailWord_836285).sum := by decide
  have hdescent : baseEnd_836285 < baseStart_836285 := by decide
  rcases family_descends (prefixWord ++ tailWord_836285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836296 : List Nat := [2, 1, 3, 1, 2, 3, 2, 1, 2, 5]
def baseStart_836296 : Nat := 118140960795 + 836296 * 2 ^ 59
def prefixEnd_836296 : Nat := 4983230072969 + 3 ^ 40 * 836296 * 2
def baseEnd_836296 : Nat := 286281211621710147835967

theorem tailTrace_836296 : CollatzResearch.WordTrace tailWord_836296 prefixEnd_836296 286281211621710147835967 := by
  unfold tailWord_836296
  simp only [CollatzResearch.WordTrace]
  refine ⟨15251110489124947415396371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20334813985499929887195161 15251110489124947415396371)
  ·
    refine ⟨22876665733687421123094557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15251110489124947415396371 22876665733687421123094557)
    ·
      refine ⟨8578749650132782921160459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22876665733687421123094557 8578749650132782921160459)
      ·
        refine ⟨12868124475199174381740689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8578749650132782921160459 12868124475199174381740689)
        ·
          refine ⟨9651093356399380786305517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12868124475199174381740689 9651093356399380786305517)
          ·
            refine ⟨3619160008649767794864569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9651093356399380786305517 3619160008649767794864569)
            ·
              refine ⟨2714370006487325846148427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3619160008649767794864569 2714370006487325846148427)
              ·
                refine ⟨4071555009730988769222641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2714370006487325846148427 4071555009730988769222641)
                ·
                  refine ⟨3053666257298241576916981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4071555009730988769222641 3053666257298241576916981)
                  ·
                    refine ⟨286281211621710147835967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3053666257298241576916981 286281211621710147835967)
                    ·
                      rfl

theorem cell22_836296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_836296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836296 prefixEnd_836296 := by exact prefixLift 836296
  have htrace : WordTrace (prefixWord ++ tailWord_836296) baseStart_836296 baseEnd_836296 := by
    simpa [prefixWord, tailWord_836296, baseEnd_836296] using wordTrace_append hprefix tailTrace_836296
  have hstable : (prefixWord ++ tailWord_836296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836296).length < 2 ^ (prefixWord ++ tailWord_836296).sum := by decide
  have hdescent : baseEnd_836296 < baseStart_836296 := by decide
  rcases family_descends (prefixWord ++ tailWord_836296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836373 : List Nat := [1, 3, 2, 1, 2, 2, 4, 1, 2, 4]
def baseStart_836373 : Nat := 118140960795 + 836373 * 2 ^ 59
def prefixEnd_836373 : Nat := 4983230072969 + 3 ^ 40 * 836373 * 2
def baseEnd_836373 : Nat := 286307570295307613660731

theorem tailTrace_836373 : CollatzResearch.WordTrace tailWord_836373 prefixEnd_836373 286307570295307613660731 := by
  unfold tailWord_836373
  simp only [CollatzResearch.WordTrace]
  refine ⟨30505029398970936981345773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20336686265980624654230515 30505029398970936981345773)
  ·
    refine ⟨11439386024614101368004665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30505029398970936981345773 11439386024614101368004665)
    ·
      refine ⟨8579539518460576026003499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11439386024614101368004665 8579539518460576026003499)
      ·
        refine ⟨12869309277690864039005249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8579539518460576026003499 12869309277690864039005249)
        ·
          refine ⟨9651981958268148029253937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12869309277690864039005249 9651981958268148029253937)
          ·
            refine ⟨7238986468701111021940453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9651981958268148029253937 7238986468701111021940453)
            ·
              refine ⟨1357309962881458316613835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7238986468701111021940453 1357309962881458316613835)
              ·
                refine ⟨2035964944322187474920753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1357309962881458316613835 2035964944322187474920753)
                ·
                  refine ⟨1526973708241640606190565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2035964944322187474920753 1526973708241640606190565)
                  ·
                    refine ⟨286307570295307613660731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1526973708241640606190565 286307570295307613660731)
                    ·
                      rfl

theorem cell22_836373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_836373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836373 prefixEnd_836373 := by exact prefixLift 836373
  have htrace : WordTrace (prefixWord ++ tailWord_836373) baseStart_836373 baseEnd_836373 := by
    simpa [prefixWord, tailWord_836373, baseEnd_836373] using wordTrace_append hprefix tailTrace_836373
  have hstable : (prefixWord ++ tailWord_836373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836373).length < 2 ^ (prefixWord ++ tailWord_836373).sum := by decide
  have hdescent : baseEnd_836373 < baseStart_836373 := by decide
  rcases family_descends (prefixWord ++ tailWord_836373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836388 : List Nat := [2, 3, 1, 3, 4, 9]
def baseStart_836388 : Nat := 118140960795 + 836388 * 2 ^ 59
def prefixEnd_836388 : Nat := 4983230072969 + 3 ^ 40 * 836388 * 2
def baseEnd_836388 : Nat := 3534724754343858944885

theorem tailTrace_836388 : CollatzResearch.WordTrace tailWord_836388 prefixEnd_836388 3534724754343858944885 := by
  unfold tailWord_836388
  simp only [CollatzResearch.WordTrace]
  refine ⟨15252788246958297271570909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20337050995944396362094545 15252788246958297271570909)
  ·
    refine ⟨5719795592609361476839091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15252788246958297271570909 5719795592609361476839091)
    ·
      refine ⟨8579693388914042215258637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5719795592609361476839091 8579693388914042215258637)
      ·
        refine ⟨3217385020842765830721989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8579693388914042215258637 3217385020842765830721989)
        ·
          refine ⟨603259691408018593260373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3217385020842765830721989 603259691408018593260373)
          ·
            refine ⟨3534724754343858944885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 603259691408018593260373 3534724754343858944885)
            ·
              rfl

theorem cell22_836388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 9].length) (baseStart_836388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836388 prefixEnd_836388 := by exact prefixLift 836388
  have htrace : WordTrace (prefixWord ++ tailWord_836388) baseStart_836388 baseEnd_836388 := by
    simpa [prefixWord, tailWord_836388, baseEnd_836388] using wordTrace_append hprefix tailTrace_836388
  have hstable : (prefixWord ++ tailWord_836388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836388).length < 2 ^ (prefixWord ++ tailWord_836388).sum := by decide
  have hdescent : baseEnd_836388 < baseStart_836388 := by decide
  rcases family_descends (prefixWord ++ tailWord_836388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836401 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 1, 8]
def baseStart_836401 : Nat := 118140960795 + 836401 * 2 ^ 59
def prefixEnd_836401 : Nat := 4983230072969 + 3 ^ 40 * 836401 * 2
def baseEnd_836401 : Nat := 286317155267524873960645

theorem tailTrace_836401 : CollatzResearch.WordTrace tailWord_836401 prefixEnd_836401 286317155267524873960645 := by
  unfold tailWord_836401
  simp only [CollatzResearch.WordTrace]
  refine ⟨30506050642869497763365057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20337367095246331842243371 30506050642869497763365057)
  ·
    refine ⟨22879537982152123322523793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30506050642869497763365057 22879537982152123322523793)
    ·
      refine ⟨17159653486614092491892845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22879537982152123322523793 17159653486614092491892845)
      ·
        refine ⟨6434870057480284684459817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17159653486614092491892845 6434870057480284684459817)
        ·
          refine ⟨4826152543110213513344863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6434870057480284684459817 4826152543110213513344863)
          ·
            refine ⟨7239228814665320270017295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4826152543110213513344863 7239228814665320270017295)
            ·
              refine ⟨10858843221997980405025943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7239228814665320270017295 10858843221997980405025943)
              ·
                refine ⟨16288264832996970607538915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10858843221997980405025943 16288264832996970607538915)
                ·
                  refine ⟨24432397249495455911308373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16288264832996970607538915 24432397249495455911308373)
                  ·
                    refine ⟨286317155267524873960645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24432397249495455911308373 286317155267524873960645)
                    ·
                      rfl

theorem cell22_836401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_836401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836401 prefixEnd_836401 := by exact prefixLift 836401
  have htrace : WordTrace (prefixWord ++ tailWord_836401) baseStart_836401 baseEnd_836401 := by
    simpa [prefixWord, tailWord_836401, baseEnd_836401] using wordTrace_append hprefix tailTrace_836401
  have hstable : (prefixWord ++ tailWord_836401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836401).length < 2 ^ (prefixWord ++ tailWord_836401).sum := by decide
  have hdescent : baseEnd_836401 < baseStart_836401 := by decide
  rcases family_descends (prefixWord ++ tailWord_836401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836437 : List Nat := [1, 3, 2, 2, 2, 1, 4, 3, 1, 3]
def baseStart_836437 : Nat := 118140960795 + 836437 * 2 ^ 59
def prefixEnd_836437 : Nat := 4983230072969 + 3 ^ 40 * 836437 * 2
def baseEnd_836437 : Nat := 286329478803232780060535

theorem tailTrace_836437 : CollatzResearch.WordTrace tailWord_836437 prefixEnd_836437 286329478803232780060535 := by
  unfold tailWord_836437
  simp only [CollatzResearch.WordTrace]
  refine ⟨30507363670739075911675565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20338242447159383941117043 30507363670739075911675565)
  ·
    refine ⟨11440261376527153466878337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30507363670739075911675565 11440261376527153466878337)
    ·
      refine ⟨8580196032395365100158753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11440261376527153466878337 8580196032395365100158753)
      ·
        refine ⟨6435147024296523825119065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8580196032395365100158753 6435147024296523825119065)
        ·
          refine ⟨4826360268222392868839299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6435147024296523825119065 4826360268222392868839299)
          ·
            refine ⟨7239540402333589303258949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4826360268222392868839299 7239540402333589303258949)
            ·
              refine ⟨1357413825437547994361053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7239540402333589303258949 1357413825437547994361053)
              ·
                refine ⟨509030184539080497885395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1357413825437547994361053 509030184539080497885395)
                ·
                  refine ⟨763545276808620746828093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 509030184539080497885395 763545276808620746828093)
                  ·
                    refine ⟨286329478803232780060535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 763545276808620746828093 286329478803232780060535)
                    ·
                      rfl

theorem cell22_836437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_836437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836437 prefixEnd_836437 := by exact prefixLift 836437
  have htrace : WordTrace (prefixWord ++ tailWord_836437) baseStart_836437 baseEnd_836437 := by
    simpa [prefixWord, tailWord_836437, baseEnd_836437] using wordTrace_append hprefix tailTrace_836437
  have hstable : (prefixWord ++ tailWord_836437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836437).length < 2 ^ (prefixWord ++ tailWord_836437).sum := by decide
  have hdescent : baseEnd_836437 < baseStart_836437 := by decide
  rcases family_descends (prefixWord ++ tailWord_836437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836450 : List Nat := [3, 3, 2, 1, 3, 1, 1, 1, 7]
def baseStart_836450 : Nat := 118140960795 + 836450 * 2 ^ 59
def prefixEnd_836450 : Nat := 4983230072969 + 3 ^ 40 * 836450 * 2
def baseEnd_836450 : Nat := 95444642989635026495165

theorem tailTrace_836450 : CollatzResearch.WordTrace tailWord_836450 prefixEnd_836450 95444642989635026495165 := by
  unfold tailWord_836450
  simp only [CollatzResearch.WordTrace]
  refine ⟨7626959454922994782974701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20338558546461319421265869 7626959454922994782974701)
  ·
    refine ⟨2860109795596123043615513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7626959454922994782974701 2860109795596123043615513)
    ·
      refine ⟨2145082346697092282711635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2860109795596123043615513 2145082346697092282711635)
      ·
        refine ⟨3217623520045638424067453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2145082346697092282711635 3217623520045638424067453)
        ·
          refine ⟨1206608820017114409025295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3217623520045638424067453 1206608820017114409025295)
          ·
            refine ⟨1809913230025671613537943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1206608820017114409025295 1809913230025671613537943)
            ·
              refine ⟨2714869845038507420306915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1809913230025671613537943 2714869845038507420306915)
              ·
                refine ⟨4072304767557761130460373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2714869845038507420306915 4072304767557761130460373)
                ·
                  refine ⟨95444642989635026495165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4072304767557761130460373 95444642989635026495165)
                  ·
                    rfl

theorem cell22_836450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_836450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836450 prefixEnd_836450 := by exact prefixLift 836450
  have htrace : WordTrace (prefixWord ++ tailWord_836450) baseStart_836450 baseEnd_836450 := by
    simpa [prefixWord, tailWord_836450, baseEnd_836450] using wordTrace_append hprefix tailTrace_836450
  have hstable : (prefixWord ++ tailWord_836450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836450).length < 2 ^ (prefixWord ++ tailWord_836450).sum := by decide
  have hdescent : baseEnd_836450 < baseStart_836450 := by decide
  rcases family_descends (prefixWord ++ tailWord_836450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836557 : List Nat := [1, 6, 3, 1, 11]
def baseStart_836557 : Nat := 118140960795 + 836557 * 2 ^ 59
def prefixEnd_836557 : Nat := 4983230072969 + 3 ^ 40 * 836557 * 2
def baseEnd_836557 : Nat := 1178479659488034843869

theorem tailTrace_836557 : CollatzResearch.WordTrace tailWord_836557 prefixEnd_836557 1178479659488034843869 := by
  unfold tailWord_836557
  simp only [CollatzResearch.WordTrace]
  refine ⟨30511740430304336406043925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20341160286869557604029283 30511740430304336406043925)
  ·
    refine ⟨1430237832670515769033309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30511740430304336406043925 1430237832670515769033309)
    ·
      refine ⟨536339187251443413387491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1430237832670515769033309 536339187251443413387491)
      ·
        refine ⟨804508780877165120081237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536339187251443413387491 804508780877165120081237)
        ·
          refine ⟨1178479659488034843869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 804508780877165120081237 1178479659488034843869)
          ·
            rfl

theorem cell22_836557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 11].length) (baseStart_836557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836557 prefixEnd_836557 := by exact prefixLift 836557
  have htrace : WordTrace (prefixWord ++ tailWord_836557) baseStart_836557 baseEnd_836557 := by
    simpa [prefixWord, tailWord_836557, baseEnd_836557] using wordTrace_append hprefix tailTrace_836557
  have hstable : (prefixWord ++ tailWord_836557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836557).length < 2 ^ (prefixWord ++ tailWord_836557).sum := by decide
  have hdescent : baseEnd_836557 < baseStart_836557 := by decide
  rcases family_descends (prefixWord ++ tailWord_836557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836613 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 8]
def baseStart_836613 : Nat := 118140960795 + 836613 * 2 ^ 59
def prefixEnd_836613 : Nat := 4983230072969 + 3 ^ 40 * 836613 * 2
def baseEnd_836613 : Nat := 95463242400008995886665

theorem tailTrace_836613 : CollatzResearch.WordTrace tailWord_836613 prefixEnd_836613 95463242400008995886665 := by
  unfold tailWord_836613
  simp only [CollatzResearch.WordTrace]
  refine ⟨30513782918101457970082493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20342521945400971980054995 30513782918101457970082493)
  ·
    refine ⟨11442668594288046738780935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30513782918101457970082493 11442668594288046738780935)
    ·
      refine ⟨17164002891432070108171403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11442668594288046738780935 17164002891432070108171403)
      ·
        refine ⟨25746004337148105162257105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17164002891432070108171403 25746004337148105162257105)
        ·
          refine ⟨19309503252861078871692829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25746004337148105162257105 19309503252861078871692829)
          ·
            refine ⟨7241063719822904576884811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19309503252861078871692829 7241063719822904576884811)
            ·
              refine ⟨10861595579734356865327217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7241063719822904576884811 10861595579734356865327217)
              ·
                refine ⟨8146196684800767648995413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10861595579734356865327217 8146196684800767648995413)
                ·
                  refine ⟨95463242400008995886665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8146196684800767648995413 95463242400008995886665)
                  ·
                    rfl

theorem cell22_836613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 8].length) (baseStart_836613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836613 prefixEnd_836613 := by exact prefixLift 836613
  have htrace : WordTrace (prefixWord ++ tailWord_836613) baseStart_836613 baseEnd_836613 := by
    simpa [prefixWord, tailWord_836613, baseEnd_836613] using wordTrace_append hprefix tailTrace_836613
  have hstable : (prefixWord ++ tailWord_836613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836613).length < 2 ^ (prefixWord ++ tailWord_836613).sum := by decide
  have hdescent : baseEnd_836613 < baseStart_836613 := by decide
  rcases family_descends (prefixWord ++ tailWord_836613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836647 : List Nat := [1, 1, 7, 1, 1, 1, 2, 2, 6]
def baseStart_836647 : Nat := 118140960795 + 836647 * 2 ^ 59
def prefixEnd_836647 : Nat := 4983230072969 + 3 ^ 40 * 836647 * 2
def baseEnd_836647 : Nat := 95467122031620744103297

theorem tailTrace_836647 : CollatzResearch.WordTrace tailWord_836647 prefixEnd_836647 95467122031620744103297 := by
  unfold tailWord_836647
  simp only [CollatzResearch.WordTrace]
  refine ⟨30515022999978281776820195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20343348666652187851213463 30515022999978281776820195)
  ·
    refine ⟨45772534499967422665230293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30515022999978281776820195 45772534499967422665230293)
    ·
      refine ⟨1072793777342986468716335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 45772534499967422665230293 1072793777342986468716335)
      ·
        refine ⟨1609190666014479703074503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1072793777342986468716335 1609190666014479703074503)
        ·
          refine ⟨2413785999021719554611755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1609190666014479703074503 2413785999021719554611755)
          ·
            refine ⟨3620678998532579331917633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2413785999021719554611755 3620678998532579331917633)
            ·
              refine ⟨2715509248899434498938225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3620678998532579331917633 2715509248899434498938225)
              ·
                refine ⟨2036631936674575874203669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2715509248899434498938225 2036631936674575874203669)
                ·
                  refine ⟨95467122031620744103297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2036631936674575874203669 95467122031620744103297)
                  ·
                    rfl

theorem cell22_836647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 6].length) (baseStart_836647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836647 prefixEnd_836647 := by exact prefixLift 836647
  have htrace : WordTrace (prefixWord ++ tailWord_836647) baseStart_836647 baseEnd_836647 := by
    simpa [prefixWord, tailWord_836647, baseEnd_836647] using wordTrace_append hprefix tailTrace_836647
  have hstable : (prefixWord ++ tailWord_836647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836647).length < 2 ^ (prefixWord ++ tailWord_836647).sum := by decide
  have hdescent : baseEnd_836647 < baseStart_836647 := by decide
  rcases family_descends (prefixWord ++ tailWord_836647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836664 : List Nat := [2, 1, 2, 1, 5, 3, 1, 3, 4]
def baseStart_836664 : Nat := 118140960795 + 836664 * 2 ^ 59
def prefixEnd_836664 : Nat := 4983230072969 + 3 ^ 40 * 836664 * 2
def baseEnd_836664 : Nat := 95469061847426618211613

theorem tailTrace_836664 : CollatzResearch.WordTrace tailWord_836664 prefixEnd_836664 95469061847426618211613 := by
  unfold tailWord_836664
  simp only [CollatzResearch.WordTrace]
  refine ⟨15257821520458346840094523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20343762027277795786792697 15257821520458346840094523)
  ·
    refine ⟨22886732280687520260141785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15257821520458346840094523 22886732280687520260141785)
    ·
      refine ⟨17165049210515640195106339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22886732280687520260141785 17165049210515640195106339)
      ·
        refine ⟨25747573815773460292659509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17165049210515640195106339 25747573815773460292659509)
        ·
          refine ⟨2413835045228761902436829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25747573815773460292659509 2413835045228761902436829)
          ·
            refine ⟨905188141960785713413811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2413835045228761902436829 905188141960785713413811)
            ·
              refine ⟨1357782212941178570120717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 905188141960785713413811 1357782212941178570120717)
              ·
                refine ⟨509168329852941963795269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1357782212941178570120717 509168329852941963795269)
                ·
                  refine ⟨95469061847426618211613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 509168329852941963795269 95469061847426618211613)
                  ·
                    rfl

theorem cell22_836664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3, 4].length) (baseStart_836664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836664 prefixEnd_836664 := by exact prefixLift 836664
  have htrace : WordTrace (prefixWord ++ tailWord_836664) baseStart_836664 baseEnd_836664 := by
    simpa [prefixWord, tailWord_836664, baseEnd_836664] using wordTrace_append hprefix tailTrace_836664
  have hstable : (prefixWord ++ tailWord_836664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836664).length < 2 ^ (prefixWord ++ tailWord_836664).sum := by decide
  have hdescent : baseEnd_836664 < baseStart_836664 := by decide
  rcases family_descends (prefixWord ++ tailWord_836664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836737 : List Nat := [1, 2, 4, 2, 2, 1, 1, 4, 5]
def baseStart_836737 : Nat := 118140960795 + 836737 * 2 ^ 59
def prefixEnd_836737 : Nat := 4983230072969 + 3 ^ 40 * 836737 * 2
def baseEnd_836737 : Nat := 95477391644710665853205

theorem tailTrace_836737 : CollatzResearch.WordTrace tailWord_836737 prefixEnd_836737 95477391644710665853205 := by
  unfold tailWord_836737
  simp only [CollatzResearch.WordTrace]
  refine ⟨30518305569652227147596465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20345537046434818098397643 30518305569652227147596465)
  ·
    refine ⟨22888729177239170360697349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30518305569652227147596465 22888729177239170360697349)
    ·
      refine ⟨4291636720732344442630753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22888729177239170360697349 4291636720732344442630753)
      ·
        refine ⟨3218727540549258331973065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4291636720732344442630753 3218727540549258331973065)
        ·
          refine ⟨2414045655411943748979799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3218727540549258331973065 2414045655411943748979799)
          ·
            refine ⟨3621068483117915623469699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2414045655411943748979799 3621068483117915623469699)
            ·
              refine ⟨5431602724676873435204549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3621068483117915623469699 5431602724676873435204549)
              ·
                refine ⟨1018425510876913769100853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5431602724676873435204549 1018425510876913769100853)
                ·
                  refine ⟨95477391644710665853205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1018425510876913769100853 95477391644710665853205)
                  ·
                    rfl

theorem cell22_836737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 5].length) (baseStart_836737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836737 prefixEnd_836737 := by exact prefixLift 836737
  have htrace : WordTrace (prefixWord ++ tailWord_836737) baseStart_836737 baseEnd_836737 := by
    simpa [prefixWord, tailWord_836737, baseEnd_836737] using wordTrace_append hprefix tailTrace_836737
  have hstable : (prefixWord ++ tailWord_836737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836737).length < 2 ^ (prefixWord ++ tailWord_836737).sum := by decide
  have hdescent : baseEnd_836737 < baseStart_836737 := by decide
  rcases family_descends (prefixWord ++ tailWord_836737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836741 : List Nat := [1, 3, 1, 1, 6, 1, 1, 4, 1, 3]
def baseStart_836741 : Nat := 118140960795 + 836741 * 2 ^ 59
def prefixEnd_836741 : Nat := 4983230072969 + 3 ^ 40 * 836741 * 2
def baseEnd_836741 : Nat := 286433544215877320459603

theorem tailTrace_836741 : CollatzResearch.WordTrace tailWord_836741 prefixEnd_836741 286433544215877320459603 := by
  unfold tailWord_836741
  simp only [CollatzResearch.WordTrace]
  refine ⟨30518451461637735830742077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20345634307758490553828051 30518451461637735830742077)
  ·
    refine ⟨11444419298114150936528279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30518451461637735830742077 11444419298114150936528279)
    ·
      refine ⟨17166628947171226404792419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11444419298114150936528279 17166628947171226404792419)
      ·
        refine ⟨25749943420756839607188629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17166628947171226404792419 25749943420756839607188629)
        ·
          refine ⟨1207028597847976856586967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25749943420756839607188629 1207028597847976856586967)
          ·
            refine ⟨1810542896771965284880451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1207028597847976856586967 1810542896771965284880451)
            ·
              refine ⟨2715814345157947927320677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1810542896771965284880451 2715814345157947927320677)
              ·
                refine ⟨509215189717115236372627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2715814345157947927320677 509215189717115236372627)
                ·
                  refine ⟨763822784575672854558941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 509215189717115236372627 763822784575672854558941)
                  ·
                    refine ⟨286433544215877320459603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 763822784575672854558941 286433544215877320459603)
                    ·
                      rfl

theorem cell22_836741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4, 1, 3].length) (baseStart_836741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836741 prefixEnd_836741 := by exact prefixLift 836741
  have htrace : WordTrace (prefixWord ++ tailWord_836741) baseStart_836741 baseEnd_836741 := by
    simpa [prefixWord, tailWord_836741, baseEnd_836741] using wordTrace_append hprefix tailTrace_836741
  have hstable : (prefixWord ++ tailWord_836741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836741).length < 2 ^ (prefixWord ++ tailWord_836741).sum := by decide
  have hdescent : baseEnd_836741 < baseStart_836741 := by decide
  rcases family_descends (prefixWord ++ tailWord_836741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836780 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 3, 5]
def baseStart_836780 : Nat := 118140960795 + 836780 * 2 ^ 59
def prefixEnd_836780 : Nat := 4983230072969 + 3 ^ 40 * 836780 * 2
def baseEnd_836780 : Nat := 286446894712894218734483

theorem tailTrace_836780 : CollatzResearch.WordTrace tailWord_836780 prefixEnd_836780 286446894712894218734483 := by
  unfold tailWord_836780
  simp only [CollatzResearch.WordTrace]
  refine ⟨15259936954248222745705897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20346582605664296994274529 15259936954248222745705897)
  ·
    refine ⟨11444952715686167059279423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15259936954248222745705897 11444952715686167059279423)
    ·
      refine ⟨17167429073529250588919135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11444952715686167059279423 17167429073529250588919135)
      ·
        refine ⟨25751143610293875883378703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17167429073529250588919135 25751143610293875883378703)
        ·
          refine ⟨38626715415440813825068055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25751143610293875883378703 38626715415440813825068055)
          ·
            refine ⟨57940073123161220737602083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38626715415440813825068055 57940073123161220737602083)
            ·
              refine ⟨86910109684741831106403125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57940073123161220737602083 86910109684741831106403125)
              ·
                refine ⟨8147822782944546666225293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86910109684741831106403125 8147822782944546666225293)
                ·
                  refine ⟨3055433543604204999834485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8147822782944546666225293 3055433543604204999834485)
                  ·
                    refine ⟨286446894712894218734483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3055433543604204999834485 286446894712894218734483)
                    ·
                      rfl

theorem cell22_836780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_836780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836780 prefixEnd_836780 := by exact prefixLift 836780
  have htrace : WordTrace (prefixWord ++ tailWord_836780) baseStart_836780 baseEnd_836780 := by
    simpa [prefixWord, tailWord_836780, baseEnd_836780] using wordTrace_append hprefix tailTrace_836780
  have hstable : (prefixWord ++ tailWord_836780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836780).length < 2 ^ (prefixWord ++ tailWord_836780).sum := by decide
  have hdescent : baseEnd_836780 < baseStart_836780 := by decide
  rcases family_descends (prefixWord ++ tailWord_836780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836825 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 1, 9]
def baseStart_836825 : Nat := 118140960795 + 836825 * 2 ^ 59
def prefixEnd_836825 : Nat := 4983230072969 + 3 ^ 40 * 836825 * 2
def baseEnd_836825 : Nat := 286462299132529101359345

theorem tailTrace_836825 : CollatzResearch.WordTrace tailWord_836825 prefixEnd_836825 286462299132529101359345 := by
  unfold tailWord_836825
  simp only [CollatzResearch.WordTrace]
  refine ⟨30521515193333418176799929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20347676795555612117866619 30521515193333418176799929)
  ·
    refine ⟨22891136395000063632599947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30521515193333418176799929 22891136395000063632599947)
    ·
      refine ⟨34336704592500095448899921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22891136395000063632599947 34336704592500095448899921)
      ·
        refine ⟨25752528444375071586674941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34336704592500095448899921 25752528444375071586674941)
        ·
          refine ⟨9657198166640651845003103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25752528444375071586674941 9657198166640651845003103)
          ·
            refine ⟨14485797249960977767504655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9657198166640651845003103 14485797249960977767504655)
            ·
              refine ⟨21728695874941466651256983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14485797249960977767504655 21728695874941466651256983)
              ·
                refine ⟨32593043812412199976885475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21728695874941466651256983 32593043812412199976885475)
                ·
                  refine ⟨48889565718618299965328213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32593043812412199976885475 48889565718618299965328213)
                  ·
                    refine ⟨286462299132529101359345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 48889565718618299965328213 286462299132529101359345)
                    ·
                      rfl

theorem cell22_836825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 9].length) (baseStart_836825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836825 prefixEnd_836825 := by exact prefixLift 836825
  have htrace : WordTrace (prefixWord ++ tailWord_836825) baseStart_836825 baseEnd_836825 := by
    simpa [prefixWord, tailWord_836825, baseEnd_836825] using wordTrace_append hprefix tailTrace_836825
  have hstable : (prefixWord ++ tailWord_836825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836825).length < 2 ^ (prefixWord ++ tailWord_836825).sum := by decide
  have hdescent : baseEnd_836825 < baseStart_836825 := by decide
  rcases family_descends (prefixWord ++ tailWord_836825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836906 : List Nat := [3, 1, 4, 2, 1, 2, 2, 2, 5]
def baseStart_836906 : Nat := 118140960795 + 836906 * 2 ^ 59
def prefixEnd_836906 : Nat := 4983230072969 + 3 ^ 40 * 836906 * 2
def baseEnd_836906 : Nat := 95496675695957296694699

theorem tailTrace_836906 : CollatzResearch.WordTrace tailWord_836906 prefixEnd_836906 95496675695957296694699 := by
  unfold tailWord_836906
  simp only [CollatzResearch.WordTrace]
  refine ⟨7631117376509992252624643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20349646337359979340332381 7631117376509992252624643)
  ·
    refine ⟨11446676064764988378936965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7631117376509992252624643 11446676064764988378936965)
    ·
      refine ⟨2146251762143435321050681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11446676064764988378936965 2146251762143435321050681)
      ·
        refine ⟨1609688821607576490788011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2146251762143435321050681 1609688821607576490788011)
        ·
          refine ⟨2414533232411364736182017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1609688821607576490788011 2414533232411364736182017)
          ·
            refine ⟨1810899924308523552136513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2414533232411364736182017 1810899924308523552136513)
            ·
              refine ⟨1358174943231392664102385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1810899924308523552136513 1358174943231392664102385)
              ·
                refine ⟨1018631207423544498076789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1358174943231392664102385 1018631207423544498076789)
                ·
                  refine ⟨95496675695957296694699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1018631207423544498076789 95496675695957296694699)
                  ·
                    rfl

theorem cell22_836906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 5].length) (baseStart_836906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836906 prefixEnd_836906 := by exact prefixLift 836906
  have htrace : WordTrace (prefixWord ++ tailWord_836906) baseStart_836906 baseEnd_836906 := by
    simpa [prefixWord, tailWord_836906, baseEnd_836906] using wordTrace_append hprefix tailTrace_836906
  have hstable : (prefixWord ++ tailWord_836906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836906).length < 2 ^ (prefixWord ++ tailWord_836906).sum := by decide
  have hdescent : baseEnd_836906 < baseStart_836906 := by decide
  rcases family_descends (prefixWord ++ tailWord_836906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836947 : List Nat := [1, 1, 1, 2, 1, 1, 7, 1, 1, 6]
def baseStart_836947 : Nat := 118140960795 + 836947 * 2 ^ 59
def prefixEnd_836947 : Nat := 4983230072969 + 3 ^ 40 * 836947 * 2
def baseEnd_836947 : Nat := 286504062225761449808971

theorem tailTrace_836947 : CollatzResearch.WordTrace tailWord_836947 prefixEnd_836947 286504062225761449808971 := by
  unfold tailWord_836947
  simp only [CollatzResearch.WordTrace]
  refine ⟨30525964898891433012741095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20350643265927622008494063 30525964898891433012741095)
  ·
    refine ⟨45788947348337149519111643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30525964898891433012741095 45788947348337149519111643)
    ·
      refine ⟨68683421022505724278667465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45788947348337149519111643 68683421022505724278667465)
      ·
        refine ⟨51512565766879293209000599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68683421022505724278667465 51512565766879293209000599)
        ·
          refine ⟨77268848650318939813500899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51512565766879293209000599 77268848650318939813500899)
          ·
            refine ⟨115903272975478409720251349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77268848650318939813500899 115903272975478409720251349)
            ·
              refine ⟨2716482960362775227818391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 115903272975478409720251349 2716482960362775227818391)
              ·
                refine ⟨4074724440544162841727587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2716482960362775227818391 4074724440544162841727587)
                ·
                  refine ⟨6112086660816244262591381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4074724440544162841727587 6112086660816244262591381)
                  ·
                    refine ⟨286504062225761449808971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6112086660816244262591381 286504062225761449808971)
                    ·
                      rfl

theorem cell22_836947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 6].length) (baseStart_836947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836947 prefixEnd_836947 := by exact prefixLift 836947
  have htrace : WordTrace (prefixWord ++ tailWord_836947) baseStart_836947 baseEnd_836947 := by
    simpa [prefixWord, tailWord_836947, baseEnd_836947] using wordTrace_append hprefix tailTrace_836947
  have hstable : (prefixWord ++ tailWord_836947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836947).length < 2 ^ (prefixWord ++ tailWord_836947).sum := by decide
  have hdescent : baseEnd_836947 < baseStart_836947 := by decide
  rcases family_descends (prefixWord ++ tailWord_836947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836949 : List Nat := [1, 3, 2, 2, 3, 1, 2, 2, 1, 5]
def baseStart_836949 : Nat := 118140960795 + 836949 * 2 ^ 59
def prefixEnd_836949 : Nat := 4983230072969 + 3 ^ 40 * 836949 * 2
def baseEnd_836949 : Nat := 286504746866634111258965

theorem tailTrace_836949 : CollatzResearch.WordTrace tailWord_836949 prefixEnd_836949 286504746866634111258965 := by
  unfold tailWord_836949
  simp only [CollatzResearch.WordTrace]
  refine ⟨30526037844884187354313901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20350691896589458236209267 30526037844884187354313901)
  ·
    refine ⟨11447264191831570257867713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30526037844884187354313901 11447264191831570257867713)
    ·
      refine ⟨8585448143873677693400785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11447264191831570257867713 8585448143873677693400785)
      ·
        refine ⟨6439086107905258270050589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8585448143873677693400785 6439086107905258270050589)
        ·
          refine ⟨2414657290464471851268971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6439086107905258270050589 2414657290464471851268971)
          ·
            refine ⟨3621985935696707776903457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2414657290464471851268971 3621985935696707776903457)
            ·
              refine ⟨2716489451772530832677593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3621985935696707776903457 2716489451772530832677593)
              ·
                refine ⟨2037367088829398124508195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2716489451772530832677593 2037367088829398124508195)
                ·
                  refine ⟨3056050633244097186762293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2037367088829398124508195 3056050633244097186762293)
                  ·
                    refine ⟨286504746866634111258965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3056050633244097186762293 286504746866634111258965)
                    ·
                      rfl

theorem cell22_836949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_836949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836949 prefixEnd_836949 := by exact prefixLift 836949
  have htrace : WordTrace (prefixWord ++ tailWord_836949) baseStart_836949 baseEnd_836949 := by
    simpa [prefixWord, tailWord_836949, baseEnd_836949] using wordTrace_append hprefix tailTrace_836949
  have hstable : (prefixWord ++ tailWord_836949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836949).length < 2 ^ (prefixWord ++ tailWord_836949).sum := by decide
  have hdescent : baseEnd_836949 < baseStart_836949 := by decide
  rcases family_descends (prefixWord ++ tailWord_836949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836951 : List Nat := [1, 1, 3, 2, 3, 3, 2, 3, 4]
def baseStart_836951 : Nat := 118140960795 + 836951 * 2 ^ 59
def prefixEnd_836951 : Nat := 4983230072969 + 3 ^ 40 * 836951 * 2
def baseEnd_836951 : Nat := 95501810502502257569653

theorem tailTrace_836951 : CollatzResearch.WordTrace tailWord_836951 prefixEnd_836951 95501810502502257569653 := by
  unfold tailWord_836951
  simp only [CollatzResearch.WordTrace]
  refine ⟨30526110790876941695886707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20350740527251294463924471 30526110790876941695886707)
  ·
    refine ⟨45789166186315412543830061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30526110790876941695886707 45789166186315412543830061)
    ·
      refine ⟨17170937319868279703936273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45789166186315412543830061 17170937319868279703936273)
      ·
        refine ⟨12878202989901209777952205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17170937319868279703936273 12878202989901209777952205)
        ·
          refine ⟨4829326121212953666732077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12878202989901209777952205 4829326121212953666732077)
          ·
            refine ⟨1810997295454857625024529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4829326121212953666732077 1810997295454857625024529)
            ·
              refine ⟨1358247971591143218768397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1810997295454857625024529 1358247971591143218768397)
              ·
                refine ⟨509342989346678707038149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1358247971591143218768397 509342989346678707038149)
                ·
                  refine ⟨95501810502502257569653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 509342989346678707038149 95501810502502257569653)
                  ·
                    rfl

theorem cell22_836951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3, 4].length) (baseStart_836951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836951 prefixEnd_836951 := by exact prefixLift 836951
  have htrace : WordTrace (prefixWord ++ tailWord_836951) baseStart_836951 baseEnd_836951 := by
    simpa [prefixWord, tailWord_836951, baseEnd_836951] using wordTrace_append hprefix tailTrace_836951
  have hstable : (prefixWord ++ tailWord_836951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836951).length < 2 ^ (prefixWord ++ tailWord_836951).sum := by decide
  have hdescent : baseEnd_836951 < baseStart_836951 := by decide
  rcases family_descends (prefixWord ++ tailWord_836951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836957 : List Nat := [1, 4, 5, 1, 2, 1, 1, 2, 5]
def baseStart_836957 : Nat := 118140960795 + 836957 * 2 ^ 59
def prefixEnd_836957 : Nat := 4983230072969 + 3 ^ 40 * 836957 * 2
def baseEnd_836957 : Nat := 95502495143374919019647

theorem tailTrace_836957 : CollatzResearch.WordTrace tailWord_836957 prefixEnd_836957 95502495143374919019647 := by
  unfold tailWord_836957
  simp only [CollatzResearch.WordTrace]
  refine ⟨30526329628855204720605125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20350886419236803147070083 30526329628855204720605125)
  ·
    refine ⟨5723686805410350885113461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30526329628855204720605125 5723686805410350885113461)
    ·
      refine ⟨536595638007220395479387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5723686805410350885113461 536595638007220395479387)
      ·
        refine ⟨804893457010830593219081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536595638007220395479387 804893457010830593219081)
        ·
          refine ⟨603670092758122944914311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 804893457010830593219081 603670092758122944914311)
          ·
            refine ⟨905505139137184417371467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603670092758122944914311 905505139137184417371467)
            ·
              refine ⟨1358257708705776626057201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 905505139137184417371467 1358257708705776626057201)
              ·
                refine ⟨1018693281529332469542901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1358257708705776626057201 1018693281529332469542901)
                ·
                  refine ⟨95502495143374919019647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1018693281529332469542901 95502495143374919019647)
                  ·
                    rfl

theorem cell22_836957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_836957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836957 prefixEnd_836957 := by exact prefixLift 836957
  have htrace : WordTrace (prefixWord ++ tailWord_836957) baseStart_836957 baseEnd_836957 := by
    simpa [prefixWord, tailWord_836957, baseEnd_836957] using wordTrace_append hprefix tailTrace_836957
  have hstable : (prefixWord ++ tailWord_836957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836957).length < 2 ^ (prefixWord ++ tailWord_836957).sum := by decide
  have hdescent : baseEnd_836957 < baseStart_836957 := by decide
  rcases family_descends (prefixWord ++ tailWord_836957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836992 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 2, 6]
def baseStart_836992 : Nat := 118140960795 + 836992 * 2 ^ 59
def prefixEnd_836992 : Nat := 4983230072969 + 3 ^ 40 * 836992 * 2
def baseEnd_836992 : Nat := 286519466645396332433833

theorem tailTrace_836992 : CollatzResearch.WordTrace tailWord_836992 prefixEnd_836992 286519466645396332433833 := by
  unfold tailWord_836992
  simp only [CollatzResearch.WordTrace]
  refine ⟨15263803091864202849064615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20351737455818937132086153 15263803091864202849064615)
  ·
    refine ⟨22895704637796304273596923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15263803091864202849064615 22895704637796304273596923)
    ·
      refine ⟨34343556956694456410395385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22895704637796304273596923 34343556956694456410395385)
      ·
        refine ⟨25757667717520842307796539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34343556956694456410395385 25757667717520842307796539)
        ·
          refine ⟨38636501576281263461694809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25757667717520842307796539 38636501576281263461694809)
          ·
            refine ⟨28977376182210947596271107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38636501576281263461694809 28977376182210947596271107)
            ·
              refine ⟨43466064273316421394406661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28977376182210947596271107 43466064273316421394406661)
              ·
                refine ⟨8149887051246829011451249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43466064273316421394406661 8149887051246829011451249)
                ·
                  refine ⟨6112415288435121758588437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8149887051246829011451249 6112415288435121758588437)
                  ·
                    refine ⟨286519466645396332433833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6112415288435121758588437 286519466645396332433833)
                    ·
                      rfl

theorem cell22_836992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 6].length) (baseStart_836992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836992 prefixEnd_836992 := by exact prefixLift 836992
  have htrace : WordTrace (prefixWord ++ tailWord_836992) baseStart_836992 baseEnd_836992 := by
    simpa [prefixWord, tailWord_836992, baseEnd_836992] using wordTrace_append hprefix tailTrace_836992
  have hstable : (prefixWord ++ tailWord_836992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836992).length < 2 ^ (prefixWord ++ tailWord_836992).sum := by decide
  have hdescent : baseEnd_836992 < baseStart_836992 := by decide
  rcases family_descends (prefixWord ++ tailWord_836992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836996 : List Nat := [2, 3, 2, 1, 1, 5, 2, 6]
def baseStart_836996 : Nat := 118140960795 + 836996 * 2 ^ 59
def prefixEnd_836996 : Nat := 4983230072969 + 3 ^ 40 * 836996 * 2
def baseEnd_836996 : Nat := 31835648436349072814869

theorem tailTrace_836996 : CollatzResearch.WordTrace tailWord_836996 prefixEnd_836996 31835648436349072814869 := by
  unfold tailWord_836996
  simp only [CollatzResearch.WordTrace]
  refine ⟨15263876037856957190637421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20351834717142609587516561 15263876037856957190637421)
  ·
    refine ⟨5723953514196358946489033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15263876037856957190637421 5723953514196358946489033)
    ·
      refine ⟨4292965135647269209866775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5723953514196358946489033 4292965135647269209866775)
      ·
        refine ⟨6439447703470903814800163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4292965135647269209866775 6439447703470903814800163)
        ·
          refine ⟨9659171555206355722200245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6439447703470903814800163 9659171555206355722200245)
          ·
            refine ⟨905547333300595848956273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9659171555206355722200245 905547333300595848956273)
            ·
              refine ⟨679160499975446886717205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 905547333300595848956273 679160499975446886717205)
              ·
                refine ⟨31835648436349072814869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 679160499975446886717205 31835648436349072814869)
                ·
                  rfl

theorem cell22_836996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 6].length) (baseStart_836996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_836996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_836996 prefixEnd_836996 := by exact prefixLift 836996
  have htrace : WordTrace (prefixWord ++ tailWord_836996) baseStart_836996 baseEnd_836996 := by
    simpa [prefixWord, tailWord_836996, baseEnd_836996] using wordTrace_append hprefix tailTrace_836996
  have hstable : (prefixWord ++ tailWord_836996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836996).length < 2 ^ (prefixWord ++ tailWord_836996).sum := by decide
  have hdescent : baseEnd_836996 < baseStart_836996 := by decide
  rcases family_descends (prefixWord ++ tailWord_836996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837024 : List Nat := [2, 1, 1, 4, 1, 2, 2, 4, 5]
def baseStart_837024 : Nat := 118140960795 + 837024 * 2 ^ 59
def prefixEnd_837024 : Nat := 4983230072969 + 3 ^ 40 * 837024 * 2
def baseEnd_837024 : Nat := 95510140299786305211245

theorem tailTrace_837024 : CollatzResearch.WordTrace tailWord_837024 prefixEnd_837024 95510140299786305211245 := by
  unfold tailWord_837024
  simp only [CollatzResearch.WordTrace]
  refine ⟨15264386659806237581647063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20352515546408316775529417 15264386659806237581647063)
  ·
    refine ⟨22896579989709356372470595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15264386659806237581647063 22896579989709356372470595)
    ·
      refine ⟨34344869984564034558705893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22896579989709356372470595 34344869984564034558705893)
      ·
        refine ⟨6439663122105756479757355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34344869984564034558705893 6439663122105756479757355)
        ·
          refine ⟨9659494683158634719636033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6439663122105756479757355 9659494683158634719636033)
          ·
            refine ⟨7244621012368976039727025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9659494683158634719636033 7244621012368976039727025)
            ·
              refine ⟨5433465759276732029795269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7244621012368976039727025 5433465759276732029795269)
              ·
                refine ⟨1018774829864387255586613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5433465759276732029795269 1018774829864387255586613)
                ·
                  refine ⟨95510140299786305211245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1018774829864387255586613 95510140299786305211245)
                  ·
                    rfl

theorem cell22_837024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 5].length) (baseStart_837024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_837024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_837024 prefixEnd_837024 := by exact prefixLift 837024
  have htrace : WordTrace (prefixWord ++ tailWord_837024) baseStart_837024 baseEnd_837024 := by
    simpa [prefixWord, tailWord_837024, baseEnd_837024] using wordTrace_append hprefix tailTrace_837024
  have hstable : (prefixWord ++ tailWord_837024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837024).length < 2 ^ (prefixWord ++ tailWord_837024).sum := by decide
  have hdescent : baseEnd_837024 < baseStart_837024 := by decide
  rcases family_descends (prefixWord ++ tailWord_837024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837116 : List Nat := [2, 2, 2, 1, 2, 1, 5, 1, 2, 4]
def baseStart_837116 : Nat := 118140960795 + 837116 * 2 ^ 59
def prefixEnd_837116 : Nat := 4983230072969 + 3 ^ 40 * 837116 * 2
def baseEnd_837116 : Nat := 286561914379501342333453

theorem tailTrace_837116 : CollatzResearch.WordTrace tailWord_837116 prefixEnd_837116 286561914379501342333453 := by
  unfold tailWord_837116
  simp only [CollatzResearch.WordTrace]
  refine ⟨15266064417639587437821601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20354752556852783250428801 15266064417639587437821601)
  ·
    refine ⟨11449548313229690578366201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15266064417639587437821601 11449548313229690578366201)
    ·
      refine ⟨8587161234922267933774651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11449548313229690578366201 8587161234922267933774651)
      ·
        refine ⟨12880741852383401900661977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8587161234922267933774651 12880741852383401900661977)
        ·
          refine ⟨9660556389287551425496483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12880741852383401900661977 9660556389287551425496483)
          ·
            refine ⟨14490834583931327138244725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9660556389287551425496483 14490834583931327138244725)
            ·
              refine ⟨1358515742243561919210443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14490834583931327138244725 1358515742243561919210443)
              ·
                refine ⟨2037773613365342878815665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1358515742243561919210443 2037773613365342878815665)
                ·
                  refine ⟨1528330210024007159111749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2037773613365342878815665 1528330210024007159111749)
                  ·
                    refine ⟨286561914379501342333453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1528330210024007159111749 286561914379501342333453)
                    ·
                      rfl

theorem cell22_837116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_837116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_837116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_837116 prefixEnd_837116 := by exact prefixLift 837116
  have htrace : WordTrace (prefixWord ++ tailWord_837116) baseStart_837116 baseEnd_837116 := by
    simpa [prefixWord, tailWord_837116, baseEnd_837116] using wordTrace_append hprefix tailTrace_837116
  have hstable : (prefixWord ++ tailWord_837116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837116).length < 2 ^ (prefixWord ++ tailWord_837116).sum := by decide
  have hdescent : baseEnd_837116 < baseStart_837116 := by decide
  rcases family_descends (prefixWord ++ tailWord_837116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837122 : List Nat := [3, 4, 1, 2, 1, 3, 2, 1, 1, 4]
def baseStart_837122 : Nat := 118140960795 + 837122 * 2 ^ 59
def prefixEnd_837122 : Nat := 4983230072969 + 3 ^ 40 * 837122 * 2
def baseEnd_837122 : Nat := 286563968302119326683435

theorem tailTrace_837122 : CollatzResearch.WordTrace tailWord_837122 prefixEnd_837122 286563968302119326683435 := by
  unfold tailWord_837122
  simp only [CollatzResearch.WordTrace]
  refine ⟨7633086918314359475090405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20354898448838291933574413 7633086918314359475090405)
  ·
    refine ⟨1431203797183942401579451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7633086918314359475090405 1431203797183942401579451)
    ·
      refine ⟨2146805695775913602369177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1431203797183942401579451 2146805695775913602369177)
      ·
        refine ⟨1610104271831935201776883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2146805695775913602369177 1610104271831935201776883)
        ·
          refine ⟨2415156407747902802665325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1610104271831935201776883 2415156407747902802665325)
          ·
            refine ⟨905683652905463550999497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2415156407747902802665325 905683652905463550999497)
            ·
              refine ⟨679262739679097663249623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 905683652905463550999497 679262739679097663249623)
              ·
                refine ⟨1018894109518646494874435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 679262739679097663249623 1018894109518646494874435)
                ·
                  refine ⟨1528341164277969742311653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1018894109518646494874435 1528341164277969742311653)
                  ·
                    refine ⟨286563968302119326683435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1528341164277969742311653 286563968302119326683435)
                    ·
                      rfl

theorem cell22_837122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_837122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_837122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_837122 prefixEnd_837122 := by exact prefixLift 837122
  have htrace : WordTrace (prefixWord ++ tailWord_837122) baseStart_837122 baseEnd_837122 := by
    simpa [prefixWord, tailWord_837122, baseEnd_837122] using wordTrace_append hprefix tailTrace_837122
  have hstable : (prefixWord ++ tailWord_837122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837122).length < 2 ^ (prefixWord ++ tailWord_837122).sum := by decide
  have hdescent : baseEnd_837122 < baseStart_837122 := by decide
  rcases family_descends (prefixWord ++ tailWord_837122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837197 : List Nat := [1, 6, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_837197 : Nat := 118140960795 + 837197 * 2 ^ 59
def prefixEnd_837197 : Nat := 4983230072969 + 3 ^ 40 * 837197 * 2
def baseEnd_837197 : Nat := 286589642334844131058205

theorem tailTrace_837197 : CollatzResearch.WordTrace tailWord_837197 prefixEnd_837197 286589642334844131058205 := by
  unfold tailWord_837197
  simp only [CollatzResearch.WordTrace]
  refine ⟨30535083147985725709341845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20356722098657150472894563 30535083147985725709341845)
  ·
    refine ⟨1431332022561830892625399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30535083147985725709341845 1431332022561830892625399)
    ·
      refine ⟨2146998033842746338938099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1431332022561830892625399 2146998033842746338938099)
      ·
        refine ⟨3220497050764119508407149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2146998033842746338938099 3220497050764119508407149)
        ·
          refine ⟨1207686394036544815652681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3220497050764119508407149 1207686394036544815652681)
          ·
            refine ⟨905764795527408611739511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1207686394036544815652681 905764795527408611739511)
            ·
              refine ⟨1358647193291112917609267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 905764795527408611739511 1358647193291112917609267)
              ·
                refine ⟨2037970789936669376413901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1358647193291112917609267 2037970789936669376413901)
                ·
                  refine ⟨764239046226251016155213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2037970789936669376413901 764239046226251016155213)
                  ·
                    refine ⟨286589642334844131058205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 764239046226251016155213 286589642334844131058205)
                    ·
                      rfl

theorem cell22_837197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_837197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_837197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_837197 prefixEnd_837197 := by exact prefixLift 837197
  have htrace : WordTrace (prefixWord ++ tailWord_837197) baseStart_837197 baseEnd_837197 := by
    simpa [prefixWord, tailWord_837197, baseEnd_837197] using wordTrace_append hprefix tailTrace_837197
  have hstable : (prefixWord ++ tailWord_837197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837197).length < 2 ^ (prefixWord ++ tailWord_837197).sum := by decide
  have hdescent : baseEnd_837197 < baseStart_837197 := by decide
  rcases family_descends (prefixWord ++ tailWord_837197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837223 : List Nat := [1, 1, 5, 1, 1, 1, 5, 2, 1, 4]
def baseStart_837223 : Nat := 118140960795 + 837223 * 2 ^ 59
def prefixEnd_837223 : Nat := 4983230072969 + 3 ^ 40 * 837223 * 2
def baseEnd_837223 : Nat := 286598542666188729908125

theorem tailTrace_837223 : CollatzResearch.WordTrace tailWord_837223 prefixEnd_837223 286598542666188729908125 := by
  unfold tailWord_837223
  simp only [CollatzResearch.WordTrace]
  refine ⟨30536031445891532149788323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20357354297261021433192215 30536031445891532149788323)
  ·
    refine ⟨45804047168837298224682485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30536031445891532149788323 45804047168837298224682485)
    ·
      refine ⟨4294129422078496708563983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45804047168837298224682485 4294129422078496708563983)
      ·
        refine ⟨6441194133117745062845975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4294129422078496708563983 6441194133117745062845975)
        ·
          refine ⟨9661791199676617594268963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6441194133117745062845975 9661791199676617594268963)
          ·
            refine ⟨14492686799514926391403445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9661791199676617594268963 14492686799514926391403445)
            ·
              refine ⟨1358689387454524349194073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14492686799514926391403445 1358689387454524349194073)
              ·
                refine ⟨1019017040590893261895555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1358689387454524349194073 1019017040590893261895555)
                ·
                  refine ⟨1528525560886339892843333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1019017040590893261895555 1528525560886339892843333)
                  ·
                    refine ⟨286598542666188729908125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1528525560886339892843333 286598542666188729908125)
                    ·
                      rfl

theorem cell22_837223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_837223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_837223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_837223 prefixEnd_837223 := by exact prefixLift 837223
  have htrace : WordTrace (prefixWord ++ tailWord_837223) baseStart_837223 baseEnd_837223 := by
    simpa [prefixWord, tailWord_837223, baseEnd_837223] using wordTrace_append hprefix tailTrace_837223
  have hstable : (prefixWord ++ tailWord_837223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837223).length < 2 ^ (prefixWord ++ tailWord_837223).sum := by decide
  have hdescent : baseEnd_837223 < baseStart_837223 := by decide
  rcases family_descends (prefixWord ++ tailWord_837223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837255 : List Nat := [1, 1, 4, 2, 1, 3, 4, 2, 4]
def baseStart_837255 : Nat := 118140960795 + 837255 * 2 ^ 59
def prefixEnd_837255 : Nat := 4983230072969 + 3 ^ 40 * 837255 * 2
def baseEnd_837255 : Nat := 95536498973383771036009

theorem tailTrace_837255 : CollatzResearch.WordTrace tailWord_837255 prefixEnd_837255 95536498973383771036009 := by
  unfold tailWord_837255
  simp only [CollatzResearch.WordTrace]
  refine ⟨30537198581775601614953219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20358132387850401076635479 30537198581775601614953219)
  ·
    refine ⟨45805797872663402422429829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30537198581775601614953219 45805797872663402422429829)
    ·
      refine ⟨8588587101124387954205593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45805797872663402422429829 8588587101124387954205593)
      ·
        refine ⟨6441440325843290965654195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8588587101124387954205593 6441440325843290965654195)
        ·
          refine ⟨9662160488764936448481293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6441440325843290965654195 9662160488764936448481293)
          ·
            refine ⟨3623310183286851168180485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9662160488764936448481293 3623310183286851168180485)
            ·
              refine ⟨679370659366284594033841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3623310183286851168180485 679370659366284594033841)
              ·
                refine ⟨509527994524713445525381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 679370659366284594033841 509527994524713445525381)
                ·
                  refine ⟨95536498973383771036009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 509527994524713445525381 95536498973383771036009)
                  ·
                    rfl

theorem cell22_837255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2, 4].length) (baseStart_837255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_837255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_837255 prefixEnd_837255 := by exact prefixLift 837255
  have htrace : WordTrace (prefixWord ++ tailWord_837255) baseStart_837255 baseEnd_837255 := by
    simpa [prefixWord, tailWord_837255, baseEnd_837255] using wordTrace_append hprefix tailTrace_837255
  have hstable : (prefixWord ++ tailWord_837255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837255).length < 2 ^ (prefixWord ++ tailWord_837255).sum := by decide
  have hdescent : baseEnd_837255 < baseStart_837255 := by decide
  rcases family_descends (prefixWord ++ tailWord_837255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837311 : List Nat := [1, 1, 2, 2, 2, 3, 3, 1, 7]
def baseStart_837311 : Nat := 118140960795 + 837311 * 2 ^ 59
def prefixEnd_837311 : Nat := 4983230072969 + 3 ^ 40 * 837311 * 2
def baseEnd_837311 : Nat := 95542888954861944569285

theorem tailTrace_837311 : CollatzResearch.WordTrace tailWord_837311 prefixEnd_837311 95542888954861944569285 := by
  unfold tailWord_837311
  simp only [CollatzResearch.WordTrace]
  refine ⟨30539241069572723178991787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20359494046381815452661191 30539241069572723178991787)
  ·
    refine ⟨45808861604359084768487681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30539241069572723178991787 45808861604359084768487681)
    ·
      refine ⟨34356646203269313576365761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45808861604359084768487681 34356646203269313576365761)
      ·
        refine ⟨25767484652451985182274321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34356646203269313576365761 25767484652451985182274321)
        ·
          refine ⟨19325613489338988886705741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25767484652451985182274321 19325613489338988886705741)
          ·
            refine ⟨7247105058502120832514653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19325613489338988886705741 7247105058502120832514653)
            ·
              refine ⟨2717664396938295312192995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7247105058502120832514653 2717664396938295312192995)
              ·
                refine ⟨4076496595407442968289493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2717664396938295312192995 4076496595407442968289493)
                ·
                  refine ⟨95542888954861944569285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4076496595407442968289493 95542888954861944569285)
                  ·
                    rfl

theorem cell22_837311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 7].length) (baseStart_837311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_837311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_837311 prefixEnd_837311 := by exact prefixLift 837311
  have htrace : WordTrace (prefixWord ++ tailWord_837311) baseStart_837311 baseEnd_837311 := by
    simpa [prefixWord, tailWord_837311, baseEnd_837311] using wordTrace_append hprefix tailTrace_837311
  have hstable : (prefixWord ++ tailWord_837311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837311).length < 2 ^ (prefixWord ++ tailWord_837311).sum := by decide
  have hdescent : baseEnd_837311 < baseStart_837311 := by decide
  rcases family_descends (prefixWord ++ tailWord_837311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837334 : List Nat := [5, 2, 1, 3, 1, 2, 2, 6]
def baseStart_837334 : Nat := 118140960795 + 837334 * 2 ^ 59
def prefixEnd_837334 : Nat := 4983230072969 + 3 ^ 40 * 837334 * 2
def baseEnd_837334 : Nat := 31848504470513493375865

theorem tailTrace_837334 : CollatzResearch.WordTrace tailWord_837334 prefixEnd_837334 31848504470513493375865 := by
  unfold tailWord_837334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1908754996780587381692441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20360053298992932071386037 1908754996780587381692441)
  ·
    refine ⟨1431566247585440536269331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1908754996780587381692441 1431566247585440536269331)
    ·
      refine ⟨2147349371378160804403997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1431566247585440536269331 2147349371378160804403997)
      ·
        refine ⟨805256014266810301651499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2147349371378160804403997 805256014266810301651499)
        ·
          refine ⟨1207884021400215452477249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 805256014266810301651499 1207884021400215452477249)
          ·
            refine ⟨905913016050161589357937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1207884021400215452477249 905913016050161589357937)
            ·
              refine ⟨679434762037621192018453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 905913016050161589357937 679434762037621192018453)
              ·
                refine ⟨31848504470513493375865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 679434762037621192018453 31848504470513493375865)
                ·
                  rfl

theorem cell22_837334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_837334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_837334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_837334 prefixEnd_837334 := by exact prefixLift 837334
  have htrace : WordTrace (prefixWord ++ tailWord_837334) baseStart_837334 baseEnd_837334 := by
    simpa [prefixWord, tailWord_837334, baseEnd_837334] using wordTrace_append hprefix tailTrace_837334
  have hstable : (prefixWord ++ tailWord_837334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837334).length < 2 ^ (prefixWord ++ tailWord_837334).sum := by decide
  have hdescent : baseEnd_837334 < baseStart_837334 := by decide
  rcases family_descends (prefixWord ++ tailWord_837334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837356 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 8]
def baseStart_837356 : Nat := 118140960795 + 837356 * 2 ^ 59
def prefixEnd_837356 : Nat := 4983230072969 + 3 ^ 40 * 837356 * 2
def baseEnd_837356 : Nat := 95548023761406905444239

theorem tailTrace_837356 : CollatzResearch.WordTrace tailWord_837356 prefixEnd_837356 95548023761406905444239 := by
  unfold tailWord_837356
  simp only [CollatzResearch.WordTrace]
  refine ⟨15270441177204847932189961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20360588236273130576253281 15270441177204847932189961)
  ·
    refine ⟨11452830882903635949142471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15270441177204847932189961 11452830882903635949142471)
    ·
      refine ⟨17179246324355453923713707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11452830882903635949142471 17179246324355453923713707)
      ·
        refine ⟨25768869486533180885570561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17179246324355453923713707 25768869486533180885570561)
        ·
          refine ⟨19326652114899885664177921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25768869486533180885570561 19326652114899885664177921)
          ·
            refine ⟨14494989086174914248133441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19326652114899885664177921 14494989086174914248133441)
            ·
              refine ⟨10871241814631185686100081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14494989086174914248133441 10871241814631185686100081)
              ·
                refine ⟨8153431360973389264575061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10871241814631185686100081 8153431360973389264575061)
                ·
                  refine ⟨95548023761406905444239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8153431360973389264575061 95548023761406905444239)
                  ·
                    rfl

theorem cell22_837356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 8].length) (baseStart_837356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_837356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_837356 prefixEnd_837356 := by exact prefixLift 837356
  have htrace : WordTrace (prefixWord ++ tailWord_837356) baseStart_837356 baseEnd_837356 := by
    simpa [prefixWord, tailWord_837356, baseEnd_837356] using wordTrace_append hprefix tailTrace_837356
  have hstable : (prefixWord ++ tailWord_837356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837356).length < 2 ^ (prefixWord ++ tailWord_837356).sum := by decide
  have hdescent : baseEnd_837356 < baseStart_837356 := by decide
  rcases family_descends (prefixWord ++ tailWord_837356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837371 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 5, 5]
def baseStart_837371 : Nat := 118140960795 + 837371 * 2 ^ 59
def prefixEnd_837371 : Nat := 4983230072969 + 3 ^ 40 * 837371 * 2
def baseEnd_837371 : Nat := 286649206090765677207671

theorem tailTrace_837371 : CollatzResearch.WordTrace tailWord_837371 prefixEnd_837371 286649206090765677207671 := by
  unfold tailWord_837371
  simp only [CollatzResearch.WordTrace]
  refine ⟨30541429449355353426175967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20360952966236902284117311 30541429449355353426175967)
  ·
    refine ⟨45812144174033030139263951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30541429449355353426175967 45812144174033030139263951)
    ·
      refine ⟨68718216261049545208895927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45812144174033030139263951 68718216261049545208895927)
      ·
        refine ⟨103077324391574317813343891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68718216261049545208895927 103077324391574317813343891)
        ·
          refine ⟨154615986587361476720015837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103077324391574317813343891 154615986587361476720015837)
          ·
            refine ⟨57980994970260553770005939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154615986587361476720015837 57980994970260553770005939)
            ·
              refine ⟨86971492455390830655008909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57980994970260553770005939 86971492455390830655008909)
              ·
                refine ⟨32614309670771561495628341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86971492455390830655008909 32614309670771561495628341)
                ·
                  refine ⟨3057591531634833890215157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32614309670771561495628341 3057591531634833890215157)
                  ·
                    refine ⟨286649206090765677207671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3057591531634833890215157 286649206090765677207671)
                    ·
                      rfl

theorem cell22_837371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 5].length) (baseStart_837371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_837371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_837371 prefixEnd_837371 := by exact prefixLift 837371
  have htrace : WordTrace (prefixWord ++ tailWord_837371) baseStart_837371 baseEnd_837371 := by
    simpa [prefixWord, tailWord_837371, baseEnd_837371] using wordTrace_append hprefix tailTrace_837371
  have hstable : (prefixWord ++ tailWord_837371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837371).length < 2 ^ (prefixWord ++ tailWord_837371).sum := by decide
  have hdescent : baseEnd_837371 < baseStart_837371 := by decide
  rcases family_descends (prefixWord ++ tailWord_837371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837450 : List Nat := [3, 1, 2, 1, 1, 1, 5, 2, 3, 3]
def baseStart_837450 : Nat := 118140960795 + 837450 * 2 ^ 59
def prefixEnd_837450 : Nat := 4983230072969 + 3 ^ 40 * 837450 * 2
def baseEnd_837450 : Nat := 286676249405235804482429

theorem tailTrace_837450 : CollatzResearch.WordTrace tailWord_837450 prefixEnd_837450 286676249405235804482429 := by
  unfold tailWord_837450
  simp only [CollatzResearch.WordTrace]
  refine ⟨7636077704017287479575451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20362873877379433278867869 7636077704017287479575451)
  ·
    refine ⟨11454116556025931219363177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7636077704017287479575451 11454116556025931219363177)
    ·
      refine ⟨8590587417019448414522383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11454116556025931219363177 8590587417019448414522383)
      ·
        refine ⟨12885881125529172621783575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8590587417019448414522383 12885881125529172621783575)
        ·
          refine ⟨19328821688293758932675363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12885881125529172621783575 19328821688293758932675363)
          ·
            refine ⟨28993232532440638399013045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19328821688293758932675363 28993232532440638399013045)
            ·
              refine ⟨2718115549916309849907473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28993232532440638399013045 2718115549916309849907473)
              ·
                refine ⟨2038586662437232387430605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2718115549916309849907473 2038586662437232387430605)
                ·
                  refine ⟨764469998413962145286477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2038586662437232387430605 764469998413962145286477)
                  ·
                    refine ⟨286676249405235804482429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 764469998413962145286477 286676249405235804482429)
                    ·
                      rfl

theorem cell22_837450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_837450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_837450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_837450 prefixEnd_837450 := by exact prefixLift 837450
  have htrace : WordTrace (prefixWord ++ tailWord_837450) baseStart_837450 baseEnd_837450 := by
    simpa [prefixWord, tailWord_837450, baseEnd_837450] using wordTrace_append hprefix tailTrace_837450
  have hstable : (prefixWord ++ tailWord_837450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837450).length < 2 ^ (prefixWord ++ tailWord_837450).sum := by decide
  have hdescent : baseEnd_837450 < baseStart_837450 := by decide
  rcases family_descends (prefixWord ++ tailWord_837450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837518 : List Nat := [4, 1, 1, 5, 1, 2, 1, 3, 1, 3]
def baseStart_837518 : Nat := 118140960795 + 837518 * 2 ^ 59
def prefixEnd_837518 : Nat := 4983230072969 + 3 ^ 40 * 837518 * 2
def baseEnd_837518 : Nat := 286699527194906293782221

theorem tailTrace_837518 : CollatzResearch.WordTrace tailWord_837518 prefixEnd_837518 286699527194906293782221 := by
  unfold tailWord_837518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3818348872477849691472151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20364527319881865021184805 3818348872477849691472151)
  ·
    refine ⟨5727523308716774537208227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3818348872477849691472151 5727523308716774537208227)
    ·
      refine ⟨8591284963075161805812341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5727523308716774537208227 8591284963075161805812341)
      ·
        refine ⟨805432965288296419294907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8591284963075161805812341 805432965288296419294907)
        ·
          refine ⟨1208149447932444628942361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 805432965288296419294907 1208149447932444628942361)
          ·
            refine ⟨906112085949333471706771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1208149447932444628942361 906112085949333471706771)
            ·
              refine ⟨1359168128924000207560157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906112085949333471706771 1359168128924000207560157)
              ·
                refine ⟨509688048346500077835059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1359168128924000207560157 509688048346500077835059)
                ·
                  refine ⟨764532072519750116752589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 509688048346500077835059 764532072519750116752589)
                  ·
                    refine ⟨286699527194906293782221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 764532072519750116752589 286699527194906293782221)
                    ·
                      rfl

theorem cell22_837518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_837518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_837518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_837518 prefixEnd_837518 := by exact prefixLift 837518
  have htrace : WordTrace (prefixWord ++ tailWord_837518) baseStart_837518 baseEnd_837518 := by
    simpa [prefixWord, tailWord_837518, baseEnd_837518] using wordTrace_append hprefix tailTrace_837518
  have hstable : (prefixWord ++ tailWord_837518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837518).length < 2 ^ (prefixWord ++ tailWord_837518).sum := by decide
  have hdescent : baseEnd_837518 < baseStart_837518 := by decide
  rcases family_descends (prefixWord ++ tailWord_837518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837585 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 7, 3]
def baseStart_837585 : Nat := 118140960795 + 837585 * 2 ^ 59
def prefixEnd_837585 : Nat := 4983230072969 + 3 ^ 40 * 837585 * 2
def baseEnd_837585 : Nat := 286722462664140452357015

theorem tailTrace_837585 : CollatzResearch.WordTrace tailWord_837585 prefixEnd_837585 286722462664140452357015 := by
  unfold tailWord_837585
  simp only [CollatzResearch.WordTrace]
  refine ⟨30549234670580067974466209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20366156447053378649644139 30549234670580067974466209)
  ·
    refine ⟨22911926002935050980849657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30549234670580067974466209 22911926002935050980849657)
    ·
      refine ⟨17183944502201288235637243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22911926002935050980849657 17183944502201288235637243)
      ·
        refine ⟨25775916753301932353455865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17183944502201288235637243 25775916753301932353455865)
        ·
          refine ⟨19331937564976449265091899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25775916753301932353455865 19331937564976449265091899)
          ·
            refine ⟨28997906347464673897637849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19331937564976449265091899 28997906347464673897637849)
            ·
              refine ⟨21748429760598505423228387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28997906347464673897637849 21748429760598505423228387)
              ·
                refine ⟨32622644640897758134842581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21748429760598505423228387 32622644640897758134842581)
                ·
                  refine ⟨764593233771041206285373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 32622644640897758134842581 764593233771041206285373)
                  ·
                    refine ⟨286722462664140452357015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 764593233771041206285373 286722462664140452357015)
                    ·
                      rfl

theorem cell22_837585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7, 3].length) (baseStart_837585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_837585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_837585 prefixEnd_837585 := by exact prefixLift 837585
  have htrace : WordTrace (prefixWord ++ tailWord_837585) baseStart_837585 baseEnd_837585 := by
    simpa [prefixWord, tailWord_837585, baseEnd_837585] using wordTrace_append hprefix tailTrace_837585
  have hstable : (prefixWord ++ tailWord_837585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837585).length < 2 ^ (prefixWord ++ tailWord_837585).sum := by decide
  have hdescent : baseEnd_837585 < baseStart_837585 := by decide
  rcases family_descends (prefixWord ++ tailWord_837585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837615 : List Nat := [1, 1, 2, 1, 4, 2, 1, 5, 5]
def baseStart_837615 : Nat := 118140960795 + 837615 * 2 ^ 59
def prefixEnd_837615 : Nat := 4983230072969 + 3 ^ 40 * 837615 * 2
def baseEnd_837615 : Nat := 95577577425743458035641

theorem tailTrace_837615 : CollatzResearch.WordTrace tailWord_837615 prefixEnd_837615 95577577425743458035641 := by
  unfold tailWord_837615
  simp only [CollatzResearch.WordTrace]
  refine ⟨30550328860471383098058299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20366885906980922065372199 30550328860471383098058299)
  ·
    refine ⟨45825493290707074647087449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30550328860471383098058299 45825493290707074647087449)
    ·
      refine ⟨34369119968030305985315587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45825493290707074647087449 34369119968030305985315587)
      ·
        refine ⟨51553679952045458977973381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34369119968030305985315587 51553679952045458977973381)
        ·
          refine ⟨9666314991008523558370009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51553679952045458977973381 9666314991008523558370009)
          ·
            refine ⟨7249736243256392668777507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9666314991008523558370009 7249736243256392668777507)
            ·
              refine ⟨10874604364884589003166261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7249736243256392668777507 10874604364884589003166261)
              ·
                refine ⟨1019494159207930219046837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10874604364884589003166261 1019494159207930219046837)
                ·
                  refine ⟨95577577425743458035641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1019494159207930219046837 95577577425743458035641)
                  ·
                    rfl

theorem cell22_837615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 5].length) (baseStart_837615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_837615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_837615 prefixEnd_837615 := by exact prefixLift 837615
  have htrace : WordTrace (prefixWord ++ tailWord_837615) baseStart_837615 baseEnd_837615 := by
    simpa [prefixWord, tailWord_837615, baseEnd_837615] using wordTrace_append hprefix tailTrace_837615
  have hstable : (prefixWord ++ tailWord_837615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837615).length < 2 ^ (prefixWord ++ tailWord_837615).sum := by decide
  have hdescent : baseEnd_837615 < baseStart_837615 := by decide
  rcases family_descends (prefixWord ++ tailWord_837615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837675 : List Nat := [1, 1, 1, 1, 2, 1, 4, 5, 1, 5]
def baseStart_837675 : Nat := 118140960795 + 837675 * 2 ^ 59
def prefixEnd_837675 : Nat := 4983230072969 + 3 ^ 40 * 837675 * 2
def baseEnd_837675 : Nat := 286753271503410217606739

theorem tailTrace_837675 : CollatzResearch.WordTrace tailWord_837675 prefixEnd_837675 286753271503410217606739 := by
  unfold tailWord_837675
  simp only [CollatzResearch.WordTrace]
  refine ⟨30552517240254013345242479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20368344826836008896828319 30552517240254013345242479)
  ·
    refine ⟨45828775860381020017863719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30552517240254013345242479 45828775860381020017863719)
    ·
      refine ⟨68743163790571530026795579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45828775860381020017863719 68743163790571530026795579)
      ·
        refine ⟨103114745685857295040193369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68743163790571530026795579 103114745685857295040193369)
        ·
          refine ⟨77336059264392971280145027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103114745685857295040193369 77336059264392971280145027)
          ·
            refine ⟨116004088896589456920217541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77336059264392971280145027 116004088896589456920217541)
            ·
              refine ⟨21750766668110523172540789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116004088896589456920217541 21750766668110523172540789)
              ·
                refine ⟨2039134375135361547425699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21750766668110523172540789 2039134375135361547425699)
                ·
                  refine ⟨3058701562703042321138549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2039134375135361547425699 3058701562703042321138549)
                  ·
                    refine ⟨286753271503410217606739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3058701562703042321138549 286753271503410217606739)
                    ·
                      rfl

theorem cell22_837675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 5].length) (baseStart_837675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_837675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_837675 prefixEnd_837675 := by exact prefixLift 837675
  have htrace : WordTrace (prefixWord ++ tailWord_837675) baseStart_837675 baseEnd_837675 := by
    simpa [prefixWord, tailWord_837675, baseEnd_837675] using wordTrace_append hprefix tailTrace_837675
  have hstable : (prefixWord ++ tailWord_837675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837675).length < 2 ^ (prefixWord ++ tailWord_837675).sum := by decide
  have hdescent : baseEnd_837675 < baseStart_837675 := by decide
  rcases family_descends (prefixWord ++ tailWord_837675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837692 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 6, 3]
def baseStart_837692 : Nat := 118140960795 + 837692 * 2 ^ 59
def prefixEnd_837692 : Nat := 4983230072969 + 3 ^ 40 * 837692 * 2
def baseEnd_837692 : Nat := 286759090950827839931687

theorem tailTrace_837692 : CollatzResearch.WordTrace tailWord_837692 prefixEnd_837692 286759090950827839931687 := by
  unfold tailWord_837692
  simp only [CollatzResearch.WordTrace]
  refine ⟨15276568640596212624305665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20368758187461616832407553 15276568640596212624305665)
  ·
    refine ⟨11457426480447159468229249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15276568640596212624305665 11457426480447159468229249)
    ·
      refine ⟨8593069860335369601171937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11457426480447159468229249 8593069860335369601171937)
      ·
        refine ⟨6444802395251527200878953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8593069860335369601171937 6444802395251527200878953)
        ·
          refine ⟨4833601796438645400659215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6444802395251527200878953 4833601796438645400659215)
          ·
            refine ⟨7250402694657968100988823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4833601796438645400659215 7250402694657968100988823)
            ·
              refine ⟨10875604041986952151483235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7250402694657968100988823 10875604041986952151483235)
              ·
                refine ⟨16313406062980428227224853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10875604041986952151483235 16313406062980428227224853)
                ·
                  refine ⟨764690909202207573151165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16313406062980428227224853 764690909202207573151165)
                  ·
                    refine ⟨286759090950827839931687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 764690909202207573151165 286759090950827839931687)
                    ·
                      rfl

theorem cell22_837692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_837692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_837692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_837692 prefixEnd_837692 := by exact prefixLift 837692
  have htrace : WordTrace (prefixWord ++ tailWord_837692) baseStart_837692 baseEnd_837692 := by
    simpa [prefixWord, tailWord_837692, baseEnd_837692] using wordTrace_append hprefix tailTrace_837692
  have hstable : (prefixWord ++ tailWord_837692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837692).length < 2 ^ (prefixWord ++ tailWord_837692).sum := by decide
  have hdescent : baseEnd_837692 < baseStart_837692 := by decide
  rcases family_descends (prefixWord ++ tailWord_837692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837709 : List Nat := [1, 6, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_837709 : Nat := 118140960795 + 837709 * 2 ^ 59
def prefixEnd_837709 : Nat := 4983230072969 + 3 ^ 40 * 837709 * 2
def baseEnd_837709 : Nat := 286764910398245462256635

theorem tailTrace_837709 : CollatzResearch.WordTrace tailWord_837709 prefixEnd_837709 286764910398245462256635 := by
  unfold tailWord_837709
  simp only [CollatzResearch.WordTrace]
  refine ⟨30553757322130837151980181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20369171548087224767986787 30553757322130837151980181)
  ·
    refine ⟨1432207374474882991499071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30553757322130837151980181 1432207374474882991499071)
    ·
      refine ⟨2148311061712324487248607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1432207374474882991499071 2148311061712324487248607)
      ·
        refine ⟨3222466592568486730872911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2148311061712324487248607 3222466592568486730872911)
        ·
          refine ⟨4833699888852730096309367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3222466592568486730872911 4833699888852730096309367)
          ·
            refine ⟨7250549833279095144464051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4833699888852730096309367 7250549833279095144464051)
            ·
              refine ⟨10875824749918642716696077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7250549833279095144464051 10875824749918642716696077)
              ·
                refine ⟨4078434281219491018761029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10875824749918642716696077 4078434281219491018761029)
                ·
                  refine ⟨764706427728654566017693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4078434281219491018761029 764706427728654566017693)
                  ·
                    refine ⟨286764910398245462256635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 764706427728654566017693 286764910398245462256635)
                    ·
                      rfl

theorem cell22_837709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_837709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_837709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_837709 prefixEnd_837709 := by exact prefixLift 837709
  have htrace : WordTrace (prefixWord ++ tailWord_837709) baseStart_837709 baseEnd_837709 := by
    simpa [prefixWord, tailWord_837709, baseEnd_837709] using wordTrace_append hprefix tailTrace_837709
  have hstable : (prefixWord ++ tailWord_837709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837709).length < 2 ^ (prefixWord ++ tailWord_837709).sum := by decide
  have hdescent : baseEnd_837709 < baseStart_837709 := by decide
  rcases family_descends (prefixWord ++ tailWord_837709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837737 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 5, 3]
def baseStart_837737 : Nat := 118140960795 + 837737 * 2 ^ 59
def prefixEnd_837737 : Nat := 4983230072969 + 3 ^ 40 * 837737 * 2
def baseEnd_837737 : Nat := 286774495370462722556549

theorem tailTrace_837737 : CollatzResearch.WordTrace tailWord_837737 prefixEnd_837737 286774495370462722556549 := by
  unfold tailWord_837737
  simp only [CollatzResearch.WordTrace]
  refine ⟨30554778566029397933999465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20369852377352931955999643 30554778566029397933999465)
  ·
    refine ⟨22916083924522048450499599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30554778566029397933999465 22916083924522048450499599)
    ·
      refine ⟨34374125886783072675749399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22916083924522048450499599 34374125886783072675749399)
      ·
        refine ⟨51561188830174609013624099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34374125886783072675749399 51561188830174609013624099)
        ·
          refine ⟨77341783245261913520436149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51561188830174609013624099 77341783245261913520436149)
          ·
            refine ⟨7250792179243304392540889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77341783245261913520436149 7250792179243304392540889)
            ·
              refine ⟨5438094134432478294405667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7250792179243304392540889 5438094134432478294405667)
              ·
                refine ⟨8157141201648717441608501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5438094134432478294405667 8157141201648717441608501)
                ·
                  refine ⟨764731987654567260150797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8157141201648717441608501 764731987654567260150797)
                  ·
                    refine ⟨286774495370462722556549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 764731987654567260150797 286774495370462722556549)
                    ·
                      rfl

theorem cell22_837737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5, 3].length) (baseStart_837737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_837737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_837737 prefixEnd_837737 := by exact prefixLift 837737
  have htrace : WordTrace (prefixWord ++ tailWord_837737) baseStart_837737 baseEnd_837737 := by
    simpa [prefixWord, tailWord_837737, baseEnd_837737] using wordTrace_append hprefix tailTrace_837737
  have hstable : (prefixWord ++ tailWord_837737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837737).length < 2 ^ (prefixWord ++ tailWord_837737).sum := by decide
  have hdescent : baseEnd_837737 < baseStart_837737 := by decide
  rcases family_descends (prefixWord ++ tailWord_837737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837767 : List Nat := [1, 1, 4, 2, 1, 1, 3, 4, 5]
def baseStart_837767 : Nat := 118140960795 + 837767 * 2 ^ 59
def prefixEnd_837767 : Nat := 4983230072969 + 3 ^ 40 * 837767 * 2
def baseEnd_837767 : Nat := 95594921661184214768819

theorem tailTrace_837767 : CollatzResearch.WordTrace tailWord_837767 prefixEnd_837767 95594921661184214768819 := by
  unfold tailWord_837767
  simp only [CollatzResearch.WordTrace]
  refine ⟨30555872755920713057591555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20370581837280475371727703 30555872755920713057591555)
  ·
    refine ⟨45833809133881069586387333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30555872755920713057591555 45833809133881069586387333)
    ·
      refine ⟨8593839212602700547447625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45833809133881069586387333 8593839212602700547447625)
      ·
        refine ⟨6445379409452025410585719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8593839212602700547447625 6445379409452025410585719)
        ·
          refine ⟨9668069114178038115878579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6445379409452025410585719 9668069114178038115878579)
          ·
            refine ⟨14502103671267057173817869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9668069114178038115878579 14502103671267057173817869)
            ·
              refine ⟨5438288876725146440181701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14502103671267057173817869 5438288876725146440181701)
              ·
                refine ⟨1019679164385964957534069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5438288876725146440181701 1019679164385964957534069)
                ·
                  refine ⟨95594921661184214768819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1019679164385964957534069 95594921661184214768819)
                  ·
                    rfl

theorem cell22_837767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 5].length) (baseStart_837767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_837767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_837767 prefixEnd_837767 := by exact prefixLift 837767
  have htrace : WordTrace (prefixWord ++ tailWord_837767) baseStart_837767 baseEnd_837767 := by
    simpa [prefixWord, tailWord_837767, baseEnd_837767] using wordTrace_append hprefix tailTrace_837767
  have hstable : (prefixWord ++ tailWord_837767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837767).length < 2 ^ (prefixWord ++ tailWord_837767).sum := by decide
  have hdescent : baseEnd_837767 < baseStart_837767 := by decide
  rcases family_descends (prefixWord ++ tailWord_837767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837797 : List Nat := [1, 3, 1, 2, 1, 3, 1, 3, 3, 4]
def baseStart_837797 : Nat := 118140960795 + 837797 * 2 ^ 59
def prefixEnd_837797 : Nat := 4983230072969 + 3 ^ 40 * 837797 * 2
def baseEnd_837797 : Nat := 286795034596642566056365

theorem tailTrace_837797 : CollatzResearch.WordTrace tailWord_837797 prefixEnd_837797 286795034596642566056365 := by
  unfold tailWord_837797
  simp only [CollatzResearch.WordTrace]
  refine ⟨30556966945812028181183645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20371311297208018787455763 30556966945812028181183645)
  ·
    refine ⟨11458862604679510567943867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30556966945812028181183645 11458862604679510567943867)
    ·
      refine ⟨17188293907019265851915801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11458862604679510567943867 17188293907019265851915801)
      ·
        refine ⟨12891220430264449388936851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17188293907019265851915801 12891220430264449388936851)
        ·
          refine ⟨19336830645396674083405277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12891220430264449388936851 19336830645396674083405277)
          ·
            refine ⟨7251311492023752781276979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19336830645396674083405277 7251311492023752781276979)
            ·
              refine ⟨10876967238035629171915469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7251311492023752781276979 10876967238035629171915469)
              ·
                refine ⟨4078862714263360939468301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10876967238035629171915469 4078862714263360939468301)
                ·
                  refine ⟨1529573517848760352300613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4078862714263360939468301 1529573517848760352300613)
                  ·
                    refine ⟨286795034596642566056365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1529573517848760352300613 286795034596642566056365)
                    ·
                      rfl

theorem cell22_837797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_837797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_837797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_837797 prefixEnd_837797 := by exact prefixLift 837797
  have htrace : WordTrace (prefixWord ++ tailWord_837797) baseStart_837797 baseEnd_837797 := by
    simpa [prefixWord, tailWord_837797, baseEnd_837797] using wordTrace_append hprefix tailTrace_837797
  have hstable : (prefixWord ++ tailWord_837797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837797).length < 2 ^ (prefixWord ++ tailWord_837797).sum := by decide
  have hdescent : baseEnd_837797 < baseStart_837797 := by decide
  rcases family_descends (prefixWord ++ tailWord_837797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837829 : List Nat := [1, 3, 1, 1, 1, 1, 6, 4, 4]
def baseStart_837829 : Nat := 118140960795 + 837829 * 2 ^ 59
def prefixEnd_837829 : Nat := 4983230072969 + 3 ^ 40 * 837829 * 2
def baseEnd_837829 : Nat := 95601996283535049752089

theorem tailTrace_837829 : CollatzResearch.WordTrace tailWord_837829 prefixEnd_837829 95601996283535049752089 := by
  unfold tailWord_837829
  simp only [CollatzResearch.WordTrace]
  refine ⟨30558134081696097646348541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20372089387797398430899027 30558134081696097646348541)
  ·
    refine ⟨11459300280636036617380703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30558134081696097646348541 11459300280636036617380703)
    ·
      refine ⟨17188950420954054926071055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11459300280636036617380703 17188950420954054926071055)
      ·
        refine ⟨25783425631431082389106583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17188950420954054926071055 25783425631431082389106583)
        ·
          refine ⟨38675138447146623583659875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25783425631431082389106583 38675138447146623583659875)
          ·
            refine ⟨58012707670719935375489813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38675138447146623583659875 58012707670719935375489813)
            ·
              refine ⟨2719345672064996970726085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58012707670719935375489813 2719345672064996970726085)
              ·
                refine ⟨509877313512186932011141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2719345672064996970726085 509877313512186932011141)
                ·
                  refine ⟨95601996283535049752089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 509877313512186932011141 95601996283535049752089)
                  ·
                    rfl

theorem cell22_837829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4, 4].length) (baseStart_837829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_837829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_837829 prefixEnd_837829 := by exact prefixLift 837829
  have htrace : WordTrace (prefixWord ++ tailWord_837829) baseStart_837829 baseEnd_837829 := by
    simpa [prefixWord, tailWord_837829, baseEnd_837829] using wordTrace_append hprefix tailTrace_837829
  have hstable : (prefixWord ++ tailWord_837829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837829).length < 2 ^ (prefixWord ++ tailWord_837829).sum := by decide
  have hdescent : baseEnd_837829 < baseStart_837829 := by decide
  rcases family_descends (prefixWord ++ tailWord_837829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837846 : List Nat := [5, 2, 1, 2, 1, 1, 2, 2, 6]
def baseStart_837846 : Nat := 118140960795 + 837846 * 2 ^ 59
def prefixEnd_837846 : Nat := 4983230072969 + 3 ^ 40 * 837846 * 2
def baseEnd_837846 : Nat := 95603936099340923860405

theorem tailTrace_837846 : CollatzResearch.WordTrace tailWord_837846 prefixEnd_837846 95603936099340923860405 := by
  unfold tailWord_837846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1909922132664656846857337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20372502748423006366478261 1909922132664656846857337)
  ·
    refine ⟨1432441599498492635143003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1909922132664656846857337 1432441599498492635143003)
    ·
      refine ⟨2148662399247738952714505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1432441599498492635143003 2148662399247738952714505)
      ·
        refine ⟨1611496799435804214535879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2148662399247738952714505 1611496799435804214535879)
        ·
          refine ⟨2417245199153706321803819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1611496799435804214535879 2417245199153706321803819)
          ·
            refine ⟨3625867798730559482705729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2417245199153706321803819 3625867798730559482705729)
            ·
              refine ⟨2719400849047919612029297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3625867798730559482705729 2719400849047919612029297)
              ·
                refine ⟨2039550636785939709021973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2719400849047919612029297 2039550636785939709021973)
                ·
                  refine ⟨95603936099340923860405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2039550636785939709021973 95603936099340923860405)
                  ·
                    rfl

theorem cell22_837846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_837846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_837846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_837846 prefixEnd_837846 := by exact prefixLift 837846
  have htrace : WordTrace (prefixWord ++ tailWord_837846) baseStart_837846 baseEnd_837846 := by
    simpa [prefixWord, tailWord_837846, baseEnd_837846] using wordTrace_append hprefix tailTrace_837846
  have hstable : (prefixWord ++ tailWord_837846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837846).length < 2 ^ (prefixWord ++ tailWord_837846).sum := by decide
  have hdescent : baseEnd_837846 < baseStart_837846 := by decide
  rcases family_descends (prefixWord ++ tailWord_837846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837857 : List Nat := [1, 2, 3, 1, 3, 1, 3, 8]
def baseStart_837857 : Nat := 118140960795 + 837857 * 2 ^ 59
def prefixEnd_837857 : Nat := 4983230072969 + 3 ^ 40 * 837857 * 2
def baseEnd_837857 : Nat := 31868397091424712172909

theorem tailTrace_837857 : CollatzResearch.WordTrace tailWord_837857 prefixEnd_837857 31868397091424712172909 := by
  unfold tailWord_837857
  simp only [CollatzResearch.WordTrace]
  refine ⟨30559155325594658428367825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20372770217063105618911883 30559155325594658428367825)
  ·
    refine ⟨22919366494195993821275869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30559155325594658428367825 22919366494195993821275869)
    ·
      refine ⟨8594762435323497682978451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22919366494195993821275869 8594762435323497682978451)
      ·
        refine ⟨12892143652985246524467677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8594762435323497682978451 12892143652985246524467677)
        ·
          refine ⟨4834553869869467446675379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12892143652985246524467677 4834553869869467446675379)
          ·
            refine ⟨7251830804804201170013069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4834553869869467446675379 7251830804804201170013069)
            ·
              refine ⟨2719436551801575438754901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7251830804804201170013069 2719436551801575438754901)
              ·
                refine ⟨31868397091424712172909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2719436551801575438754901 31868397091424712172909)
                ·
                  rfl

theorem cell22_837857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 8].length) (baseStart_837857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_837857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_837857 prefixEnd_837857 := by exact prefixLift 837857
  have htrace : WordTrace (prefixWord ++ tailWord_837857) baseStart_837857 baseEnd_837857 := by
    simpa [prefixWord, tailWord_837857, baseEnd_837857] using wordTrace_append hprefix tailTrace_837857
  have hstable : (prefixWord ++ tailWord_837857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837857).length < 2 ^ (prefixWord ++ tailWord_837857).sum := by decide
  have hdescent : baseEnd_837857 < baseStart_837857 := by decide
  rcases family_descends (prefixWord ++ tailWord_837857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837863 : List Nat := [1, 1, 5, 3, 1, 3, 1, 3, 4]
def baseStart_837863 : Nat := 118140960795 + 837863 * 2 ^ 59
def prefixEnd_837863 : Nat := 4983230072969 + 3 ^ 40 * 837863 * 2
def baseEnd_837863 : Nat := 95605875915146797968721

theorem tailTrace_837863 : CollatzResearch.WordTrace tailWord_837863 prefixEnd_837863 95605875915146797968721 := by
  unfold tailWord_837863
  simp only [CollatzResearch.WordTrace]
  refine ⟨30559374163572921453086243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20372916109048614302057495 30559374163572921453086243)
  ·
    refine ⟨45839061245359382179629365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30559374163572921453086243 45839061245359382179629365)
    ·
      refine ⟨4297411991752442079340253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45839061245359382179629365 4297411991752442079340253)
      ·
        refine ⟨1611529496907165779752595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4297411991752442079340253 1611529496907165779752595)
        ·
          refine ⟨2417294245360748669628893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1611529496907165779752595 2417294245360748669628893)
          ·
            refine ⟨906485342010280751110835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2417294245360748669628893 906485342010280751110835)
            ·
              refine ⟨1359728013015421126666253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906485342010280751110835 1359728013015421126666253)
              ·
                refine ⟨509898004880782922499845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1359728013015421126666253 509898004880782922499845)
                ·
                  refine ⟨95605875915146797968721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 509898004880782922499845 95605875915146797968721)
                  ·
                    rfl

theorem cell22_837863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3, 4].length) (baseStart_837863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_837863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_837863 prefixEnd_837863 := by exact prefixLift 837863
  have htrace : WordTrace (prefixWord ++ tailWord_837863) baseStart_837863 baseEnd_837863 := by
    simpa [prefixWord, tailWord_837863, baseEnd_837863] using wordTrace_append hprefix tailTrace_837863
  have hstable : (prefixWord ++ tailWord_837863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837863).length < 2 ^ (prefixWord ++ tailWord_837863).sum := by decide
  have hdescent : baseEnd_837863 < baseStart_837863 := by decide
  rcases family_descends (prefixWord ++ tailWord_837863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837874 : List Nat := [3, 2, 1, 3, 2, 3, 8]
def baseStart_837874 : Nat := 118140960795 + 837874 * 2 ^ 59
def prefixEnd_837874 : Nat := 4983230072969 + 3 ^ 40 * 837874 * 2
def baseEnd_837874 : Nat := 10623014565564445625227

theorem tailTrace_837874 : CollatzResearch.WordTrace tailWord_837874 prefixEnd_837874 10623014565564445625227 := by
  unfold tailWord_837874
  simp only [CollatzResearch.WordTrace]
  refine ⟨7639943841633267582934169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20373183577688713554491117 7639943841633267582934169)
  ·
    refine ⟨5729957881224950687200627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7639943841633267582934169 5729957881224950687200627)
    ·
      refine ⟨8594936821837426030800941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5729957881224950687200627 8594936821837426030800941)
      ·
        refine ⟨3223101308189034761550353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8594936821837426030800941 3223101308189034761550353)
        ·
          refine ⟨2417325981141776071162765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3223101308189034761550353 2417325981141776071162765)
          ·
            refine ⟨906497242928166026686037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2417325981141776071162765 906497242928166026686037)
            ·
              refine ⟨10623014565564445625227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 906497242928166026686037 10623014565564445625227)
              ·
                rfl

theorem cell22_837874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 8].length) (baseStart_837874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_837874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_837874 prefixEnd_837874 := by exact prefixLift 837874
  have htrace : WordTrace (prefixWord ++ tailWord_837874) baseStart_837874 baseEnd_837874 := by
    simpa [prefixWord, tailWord_837874, baseEnd_837874] using wordTrace_append hprefix tailTrace_837874
  have hstable : (prefixWord ++ tailWord_837874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837874).length < 2 ^ (prefixWord ++ tailWord_837874).sum := by decide
  have hdescent : baseEnd_837874 < baseStart_837874 := by decide
  rcases family_descends (prefixWord ++ tailWord_837874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837887 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 2, 6]
def baseStart_837887 : Nat := 118140960795 + 837887 * 2 ^ 59
def prefixEnd_837887 : Nat := 4983230072969 + 3 ^ 40 * 837887 * 2
def baseEnd_837887 : Nat := 286825843435912331306089

theorem tailTrace_837887 : CollatzResearch.WordTrace tailWord_837887 prefixEnd_837887 286825843435912331306089 := by
  unfold tailWord_837887
  simp only [CollatzResearch.WordTrace]
  refine ⟨30560249515485973551959915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20373499676990649034639943 30560249515485973551959915)
  ·
    refine ⟨45840374273228960327939873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30560249515485973551959915 45840374273228960327939873)
    ·
      refine ⟨34380280704921720245954905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45840374273228960327939873 34380280704921720245954905)
      ·
        refine ⟨25785210528691290184466179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34380280704921720245954905 25785210528691290184466179)
        ·
          refine ⟨38677815793036935276699269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25785210528691290184466179 38677815793036935276699269)
          ·
            refine ⟨7252090461194425364381113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38677815793036935276699269 7252090461194425364381113)
            ·
              refine ⟨5439067845895819023285835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7252090461194425364381113 5439067845895819023285835)
              ·
                refine ⟨8158601768843728534928753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5439067845895819023285835 8158601768843728534928753)
                ·
                  refine ⟨6118951326632796401196565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8158601768843728534928753 6118951326632796401196565)
                  ·
                    refine ⟨286825843435912331306089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6118951326632796401196565 286825843435912331306089)
                    ·
                      rfl

theorem cell22_837887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 6].length) (baseStart_837887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_837887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_837887 prefixEnd_837887 := by exact prefixLift 837887
  have htrace : WordTrace (prefixWord ++ tailWord_837887) baseStart_837887 baseEnd_837887 := by
    simpa [prefixWord, tailWord_837887, baseEnd_837887] using wordTrace_append hprefix tailTrace_837887
  have hstable : (prefixWord ++ tailWord_837887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837887).length < 2 ^ (prefixWord ++ tailWord_837887).sum := by decide
  have hdescent : baseEnd_837887 < baseStart_837887 := by decide
  rcases family_descends (prefixWord ++ tailWord_837887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837940 : List Nat := [2, 5, 1, 1, 1, 3, 1, 4, 1, 3]
def baseStart_837940 : Nat := 118140960795 + 837940 * 2 ^ 59
def prefixEnd_837940 : Nat := 4983230072969 + 3 ^ 40 * 837940 * 2
def baseEnd_837940 : Nat := 286843986419037859730927

theorem tailTrace_837940 : CollatzResearch.WordTrace tailWord_837940 prefixEnd_837940 286843986419037859730927 := by
  unfold tailWord_837940
  simp only [CollatzResearch.WordTrace]
  refine ⟨15281091292146981801819637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20374788389529309069092849 15281091292146981801819637)
  ·
    refine ⟨1432602308638779543920591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15281091292146981801819637 1432602308638779543920591)
    ·
      refine ⟨2148903462958169315880887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1432602308638779543920591 2148903462958169315880887)
      ·
        refine ⟨3223355194437253973821331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2148903462958169315880887 3223355194437253973821331)
        ·
          refine ⟨4835032791655880960731997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3223355194437253973821331 4835032791655880960731997)
          ·
            refine ⟨1813137296870955360274499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4835032791655880960731997 1813137296870955360274499)
            ·
              refine ⟨2719705945306433040411749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1813137296870955360274499 2719705945306433040411749)
              ·
                refine ⟨509944864744956195077203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2719705945306433040411749 509944864744956195077203)
                ·
                  refine ⟨764917297117434292615805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 509944864744956195077203 764917297117434292615805)
                  ·
                    refine ⟨286843986419037859730927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 764917297117434292615805 286843986419037859730927)
                    ·
                      rfl

theorem cell22_837940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_837940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_837940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_837940 prefixEnd_837940 := by exact prefixLift 837940
  have htrace : WordTrace (prefixWord ++ tailWord_837940) baseStart_837940 baseEnd_837940 := by
    simpa [prefixWord, tailWord_837940, baseEnd_837940] using wordTrace_append hprefix tailTrace_837940
  have hstable : (prefixWord ++ tailWord_837940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837940).length < 2 ^ (prefixWord ++ tailWord_837940).sum := by decide
  have hdescent : baseEnd_837940 < baseStart_837940 := by decide
  rcases family_descends (prefixWord ++ tailWord_837940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837964 : List Nat := [2, 2, 1, 3, 2, 1, 3, 2, 6]
def baseStart_837964 : Nat := 118140960795 + 837964 * 2 ^ 59
def prefixEnd_837964 : Nat := 4983230072969 + 3 ^ 40 * 837964 * 2
def baseEnd_837964 : Nat := 95617400703169932376951

theorem tailTrace_837964 : CollatzResearch.WordTrace tailWord_837964 prefixEnd_837964 95617400703169932376951 := by
  unfold tailWord_837964
  simp only [CollatzResearch.WordTrace]
  refine ⟨15281528968103507851256473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20375371957471343801675297 15281528968103507851256473)
  ·
    refine ⟨11461146726077630888442355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15281528968103507851256473 11461146726077630888442355)
    ·
      refine ⟨17191720089116446332663533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11461146726077630888442355 17191720089116446332663533)
      ·
        refine ⟨6446895033418667374748825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17191720089116446332663533 6446895033418667374748825)
        ·
          refine ⟨4835171275064000531061619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6446895033418667374748825 4835171275064000531061619)
          ·
            refine ⟨7252756912596000796592429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4835171275064000531061619 7252756912596000796592429)
            ·
              refine ⟨2719783842223500298722161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7252756912596000796592429 2719783842223500298722161)
              ·
                refine ⟨2039837881667625224041621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2719783842223500298722161 2039837881667625224041621)
                ·
                  refine ⟨95617400703169932376951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2039837881667625224041621 95617400703169932376951)
                  ·
                    rfl

theorem cell22_837964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 6].length) (baseStart_837964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_837964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_837964 prefixEnd_837964 := by exact prefixLift 837964
  have htrace : WordTrace (prefixWord ++ tailWord_837964) baseStart_837964 baseEnd_837964 := by
    simpa [prefixWord, tailWord_837964, baseEnd_837964] using wordTrace_append hprefix tailTrace_837964
  have hstable : (prefixWord ++ tailWord_837964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837964).length < 2 ^ (prefixWord ++ tailWord_837964).sum := by decide
  have hdescent : baseEnd_837964 < baseStart_837964 := by decide
  rcases family_descends (prefixWord ++ tailWord_837964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838024 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 2, 7]
def baseStart_838024 : Nat := 118140960795 + 838024 * 2 ^ 59
def prefixEnd_838024 : Nat := 4983230072969 + 3 ^ 40 * 838024 * 2
def baseEnd_838024 : Nat := 286872741335689640630669

theorem tailTrace_838024 : CollatzResearch.WordTrace tailWord_838024 prefixEnd_838024 286872741335689640630669 := by
  unfold tailWord_838024
  simp only [CollatzResearch.WordTrace]
  refine ⟨15282623157994822974848563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20376830877326430633131417 15282623157994822974848563)
  ·
    refine ⟨22923934736992234462272845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15282623157994822974848563 22923934736992234462272845)
    ·
      refine ⟨8596475526372087923352317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22923934736992234462272845 8596475526372087923352317)
      ·
        refine ⟨3223678322389532971257119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8596475526372087923352317 3223678322389532971257119)
        ·
          refine ⟨4835517483584299456885679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3223678322389532971257119 4835517483584299456885679)
          ·
            refine ⟨7253276225376449185328519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4835517483584299456885679 7253276225376449185328519)
            ·
              refine ⟨10879914338064673777992779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7253276225376449185328519 10879914338064673777992779)
              ·
                refine ⟨16319871507097010666989169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10879914338064673777992779 16319871507097010666989169)
                ·
                  refine ⟨12239903630322758000241877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16319871507097010666989169 12239903630322758000241877)
                  ·
                    refine ⟨286872741335689640630669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12239903630322758000241877 286872741335689640630669)
                    ·
                      rfl

theorem cell22_838024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_838024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838024 prefixEnd_838024 := by exact prefixLift 838024
  have htrace : WordTrace (prefixWord ++ tailWord_838024) baseStart_838024 baseEnd_838024 := by
    simpa [prefixWord, tailWord_838024, baseEnd_838024] using wordTrace_append hprefix tailTrace_838024
  have hstable : (prefixWord ++ tailWord_838024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838024).length < 2 ^ (prefixWord ++ tailWord_838024).sum := by decide
  have hdescent : baseEnd_838024 < baseStart_838024 := by decide
  rcases family_descends (prefixWord ++ tailWord_838024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838071 : List Nat := [1, 1, 3, 1, 3, 4, 1, 3, 5]
def baseStart_838071 : Nat := 118140960795 + 838071 * 2 ^ 59
def prefixEnd_838071 : Nat := 4983230072969 + 3 ^ 40 * 838071 * 2
def baseEnd_838071 : Nat := 95629610132065728235175

theorem tailTrace_838071 : CollatzResearch.WordTrace tailWord_838071 prefixEnd_838071 95629610132065728235175 := by
  unfold tailWord_838071
  simp only [CollatzResearch.WordTrace]
  refine ⟨30566960546819372976658067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20377973697879581984438711 30566960546819372976658067)
  ·
    refine ⟨45850440820229059464987101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30566960546819372976658067 45850440820229059464987101)
    ·
      refine ⟨17193915307585897299370163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45850440820229059464987101 17193915307585897299370163)
      ·
        refine ⟨25790872961378845949055245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17193915307585897299370163 25790872961378845949055245)
        ·
          refine ⟨9671577360517067230895717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25790872961378845949055245 9671577360517067230895717)
          ·
            refine ⟨1813420755096950105792947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9671577360517067230895717 1813420755096950105792947)
            ·
              refine ⟨2720131132645425158689421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1813420755096950105792947 2720131132645425158689421)
              ·
                refine ⟨1020049174742034434508533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2720131132645425158689421 1020049174742034434508533)
                ·
                  refine ⟨95629610132065728235175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1020049174742034434508533 95629610132065728235175)
                  ·
                    rfl

theorem cell22_838071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 5].length) (baseStart_838071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838071 prefixEnd_838071 := by exact prefixLift 838071
  have htrace : WordTrace (prefixWord ++ tailWord_838071) baseStart_838071 baseEnd_838071 := by
    simpa [prefixWord, tailWord_838071, baseEnd_838071] using wordTrace_append hprefix tailTrace_838071
  have hstable : (prefixWord ++ tailWord_838071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838071).length < 2 ^ (prefixWord ++ tailWord_838071).sum := by decide
  have hdescent : baseEnd_838071 < baseStart_838071 := by decide
  rcases family_descends (prefixWord ++ tailWord_838071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838131 : List Nat := [1, 1, 1, 2, 2, 2, 6, 1, 1, 5]
def baseStart_838131 : Nat := 118140960795 + 838131 * 2 ^ 59
def prefixEnd_838131 : Nat := 4983230072969 + 3 ^ 40 * 838131 * 2
def baseEnd_838131 : Nat := 286909369622377028205341

theorem tailTrace_838131 : CollatzResearch.WordTrace tailWord_838131 prefixEnd_838131 286909369622377028205341 := by
  unfold tailWord_838131
  simp only [CollatzResearch.WordTrace]
  refine ⟨30569148926602003223842247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20379432617734668815894831 30569148926602003223842247)
  ·
    refine ⟨45853723389903004835763371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30569148926602003223842247 45853723389903004835763371)
    ·
      refine ⟨68780585084854507253645057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45853723389903004835763371 68780585084854507253645057)
      ·
        refine ⟨51585438813640880440233793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68780585084854507253645057 51585438813640880440233793)
        ·
          refine ⟨38689079110230660330175345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51585438813640880440233793 38689079110230660330175345)
          ·
            refine ⟨29016809332672995247631509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38689079110230660330175345 29016809332672995247631509)
            ·
              refine ⟨1360162937469046652232727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29016809332672995247631509 1360162937469046652232727)
              ·
                refine ⟨2040244406203569978349091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1360162937469046652232727 2040244406203569978349091)
                ·
                  refine ⟨3060366609305354967523637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2040244406203569978349091 3060366609305354967523637)
                  ·
                    refine ⟨286909369622377028205341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3060366609305354967523637 286909369622377028205341)
                    ·
                      rfl

theorem cell22_838131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 5].length) (baseStart_838131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838131 prefixEnd_838131 := by exact prefixLift 838131
  have htrace : WordTrace (prefixWord ++ tailWord_838131) baseStart_838131 baseEnd_838131 := by
    simpa [prefixWord, tailWord_838131, baseEnd_838131] using wordTrace_append hprefix tailTrace_838131
  have hstable : (prefixWord ++ tailWord_838131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838131).length < 2 ^ (prefixWord ++ tailWord_838131).sum := by decide
  have hdescent : baseEnd_838131 < baseStart_838131 := by decide
  rcases family_descends (prefixWord ++ tailWord_838131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838148 : List Nat := [2, 3, 2, 3, 1, 1, 2, 2, 1, 5]
def baseStart_838148 : Nat := 118140960795 + 838148 * 2 ^ 59
def prefixEnd_838148 : Nat := 4983230072969 + 3 ^ 40 * 838148 * 2
def baseEnd_838148 : Nat := 286915189069794650530289

theorem tailTrace_838148 : CollatzResearch.WordTrace tailWord_838148 prefixEnd_838148 286915189069794650530289 := by
  unfold tailWord_838148
  simp only [CollatzResearch.WordTrace]
  refine ⟨15284884483770207563605549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20379845978360276751474065 15284884483770207563605549)
  ·
    refine ⟨5731831681413827836352081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15284884483770207563605549 5731831681413827836352081)
    ·
      refine ⟨4298873761060370877264061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5731831681413827836352081 4298873761060370877264061)
      ·
        refine ⟨1612077660397639078974023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4298873761060370877264061 1612077660397639078974023)
        ·
          refine ⟨2418116490596458618461035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1612077660397639078974023 2418116490596458618461035)
          ·
            refine ⟨3627174735894687927691553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2418116490596458618461035 3627174735894687927691553)
            ·
              refine ⟨2720381051921015945768665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3627174735894687927691553 2720381051921015945768665)
              ·
                refine ⟨2040285788940761959326499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2720381051921015945768665 2040285788940761959326499)
                ·
                  refine ⟨3060428683411142938989749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2040285788940761959326499 3060428683411142938989749)
                  ·
                    refine ⟨286915189069794650530289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3060428683411142938989749 286915189069794650530289)
                    ·
                      rfl

theorem cell22_838148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_838148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838148 prefixEnd_838148 := by exact prefixLift 838148
  have htrace : WordTrace (prefixWord ++ tailWord_838148) baseStart_838148 baseEnd_838148 := by
    simpa [prefixWord, tailWord_838148, baseEnd_838148] using wordTrace_append hprefix tailTrace_838148
  have hstable : (prefixWord ++ tailWord_838148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838148).length < 2 ^ (prefixWord ++ tailWord_838148).sum := by decide
  have hdescent : baseEnd_838148 < baseStart_838148 := by decide
  rcases family_descends (prefixWord ++ tailWord_838148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838193 : List Nat := [1, 2, 2, 3, 1, 1, 4, 2, 3, 3]
def baseStart_838193 : Nat := 118140960795 + 838193 * 2 ^ 59
def prefixEnd_838193 : Nat := 4983230072969 + 3 ^ 40 * 838193 * 2
def baseEnd_838193 : Nat := 286930593489429533155151

theorem tailTrace_838193 : CollatzResearch.WordTrace tailWord_838193 prefixEnd_838193 286930593489429533155151 := by
  unfold tailWord_838193
  simp only [CollatzResearch.WordTrace]
  refine ⟨30571410252377387812599233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20380940168251591875066155 30571410252377387812599233)
  ·
    refine ⟨22928557689283040859449425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30571410252377387812599233 22928557689283040859449425)
    ·
      refine ⟨17196418266962280644587069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22928557689283040859449425 17196418266962280644587069)
      ·
        refine ⟨6448656850110855241720151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17196418266962280644587069 6448656850110855241720151)
        ·
          refine ⟨9672985275166282862580227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6448656850110855241720151 9672985275166282862580227)
          ·
            refine ⟨14509477912749424293870341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9672985275166282862580227 14509477912749424293870341)
            ·
              refine ⟨2720527108640517055100689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14509477912749424293870341 2720527108640517055100689)
              ·
                refine ⟨2040395331480387791325517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2720527108640517055100689 2040395331480387791325517)
                ·
                  refine ⟨765148249305145421747069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2040395331480387791325517 765148249305145421747069)
                  ·
                    refine ⟨286930593489429533155151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 765148249305145421747069 286930593489429533155151)
                    ·
                      rfl

theorem cell22_838193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3, 3].length) (baseStart_838193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838193 prefixEnd_838193 := by exact prefixLift 838193
  have htrace : WordTrace (prefixWord ++ tailWord_838193) baseStart_838193 baseEnd_838193 := by
    simpa [prefixWord, tailWord_838193, baseEnd_838193] using wordTrace_append hprefix tailTrace_838193
  have hstable : (prefixWord ++ tailWord_838193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838193).length < 2 ^ (prefixWord ++ tailWord_838193).sum := by decide
  have hdescent : baseEnd_838193 < baseStart_838193 := by decide
  rcases family_descends (prefixWord ++ tailWord_838193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838212 : List Nat := [2, 3, 5, 1, 1, 2, 8]
def baseStart_838212 : Nat := 118140960795 + 838212 * 2 ^ 59
def prefixEnd_838212 : Nat := 4983230072969 + 3 ^ 40 * 838212 * 2
def baseEnd_838212 : Nat := 10627299910285919145559

theorem tailTrace_838212 : CollatzResearch.WordTrace tailWord_838212 prefixEnd_838212 10627299910285919145559 := by
  unfold tailWord_838212
  simp only [CollatzResearch.WordTrace]
  refine ⟨15286051619654277028770445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20381402159539036038360593 15286051619654277028770445)
  ·
    refine ⟨5732269357370353885788917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15286051619654277028770445 5732269357370353885788917)
    ·
      refine ⟨537400252253470676792711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5732269357370353885788917 537400252253470676792711)
      ·
        refine ⟨806100378380206015189067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537400252253470676792711 806100378380206015189067)
        ·
          refine ⟨1209150567570309022783601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 806100378380206015189067 1209150567570309022783601)
          ·
            refine ⟨906862925677731767087701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1209150567570309022783601 906862925677731767087701)
            ·
              refine ⟨10627299910285919145559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 906862925677731767087701 10627299910285919145559)
              ·
                rfl

theorem cell22_838212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 8].length) (baseStart_838212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838212 prefixEnd_838212 := by exact prefixLift 838212
  have htrace : WordTrace (prefixWord ++ tailWord_838212) baseStart_838212 baseEnd_838212 := by
    simpa [prefixWord, tailWord_838212, baseEnd_838212] using wordTrace_append hprefix tailTrace_838212
  have hstable : (prefixWord ++ tailWord_838212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838212).length < 2 ^ (prefixWord ++ tailWord_838212).sum := by decide
  have hdescent : baseEnd_838212 < baseStart_838212 := by decide
  rcases family_descends (prefixWord ++ tailWord_838212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838281 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 3, 6]
def baseStart_838281 : Nat := 118140960795 + 838281 * 2 ^ 59
def prefixEnd_838281 : Nat := 4983230072969 + 3 ^ 40 * 838281 * 2
def baseEnd_838281 : Nat := 286960717687826636954881

theorem tailTrace_838281 : CollatzResearch.WordTrace tailWord_838281 prefixEnd_838281 286960717687826636954881 := by
  unfold tailWord_838281
  simp only [CollatzResearch.WordTrace]
  refine ⟨30574619876058578841802697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20383079917372385894535131 30574619876058578841802697)
  ·
    refine ⟨22930964907043934131352023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30574619876058578841802697 22930964907043934131352023)
    ·
      refine ⟨34396447360565901197028035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22930964907043934131352023 34396447360565901197028035)
      ·
        refine ⟨51594671040848851795542053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34396447360565901197028035 51594671040848851795542053)
        ·
          refine ⟨9674000820159159711664135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51594671040848851795542053 9674000820159159711664135)
          ·
            refine ⟨14511001230238739567496203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9674000820159159711664135 14511001230238739567496203)
            ·
              refine ⟨21766501845358109351244305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14511001230238739567496203 21766501845358109351244305)
              ·
                refine ⟨16324876384018582013433229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21766501845358109351244305 16324876384018582013433229)
                ·
                  refine ⟨6121828644006968255037461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16324876384018582013433229 6121828644006968255037461)
                  ·
                    refine ⟨286960717687826636954881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6121828644006968255037461 286960717687826636954881)
                    ·
                      rfl

theorem cell22_838281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 6].length) (baseStart_838281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838281 prefixEnd_838281 := by exact prefixLift 838281
  have htrace : WordTrace (prefixWord ++ tailWord_838281) baseStart_838281 baseEnd_838281 := by
    simpa [prefixWord, tailWord_838281, baseEnd_838281] using wordTrace_append hprefix tailTrace_838281
  have hstable : (prefixWord ++ tailWord_838281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838281).length < 2 ^ (prefixWord ++ tailWord_838281).sum := by decide
  have hdescent : baseEnd_838281 < baseStart_838281 := by decide
  rcases family_descends (prefixWord ++ tailWord_838281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838300 : List Nat := [2, 2, 3, 2, 2, 2, 2, 1, 1, 5]
def baseStart_838300 : Nat := 118140960795 + 838300 * 2 ^ 59
def prefixEnd_838300 : Nat := 4983230072969 + 3 ^ 40 * 838300 * 2
def baseEnd_838300 : Nat := 286967221776116920729823

theorem tailTrace_838300 : CollatzResearch.WordTrace tailWord_838300 prefixEnd_838300 286967221776116920729823 := by
  unfold tailWord_838300
  simp only [CollatzResearch.WordTrace]
  refine ⟨15287656431494872543372177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20383541908659830057829569 15287656431494872543372177)
  ·
    refine ⟨11465742323621154407529133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15287656431494872543372177 11465742323621154407529133)
    ·
      refine ⟨4299653371357932902823425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11465742323621154407529133 4299653371357932902823425)
      ·
        refine ⟨3224740028518449677117569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4299653371357932902823425 3224740028518449677117569)
        ·
          refine ⟨2418555021388837257838177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3224740028518449677117569 2418555021388837257838177)
          ·
            refine ⟨1813916266041627943378633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2418555021388837257838177 1813916266041627943378633)
            ·
              refine ⟨1360437199531220957533975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1813916266041627943378633 1360437199531220957533975)
              ·
                refine ⟨2040655799296831436300963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1360437199531220957533975 2040655799296831436300963)
                ·
                  refine ⟨3060983698945247154451445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2040655799296831436300963 3060983698945247154451445)
                  ·
                    refine ⟨286967221776116920729823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3060983698945247154451445 286967221776116920729823)
                    ·
                      rfl

theorem cell22_838300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_838300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838300 prefixEnd_838300 := by exact prefixLift 838300
  have htrace : WordTrace (prefixWord ++ tailWord_838300) baseStart_838300 baseEnd_838300 := by
    simpa [prefixWord, tailWord_838300, baseEnd_838300] using wordTrace_append hprefix tailTrace_838300
  have hstable : (prefixWord ++ tailWord_838300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838300).length < 2 ^ (prefixWord ++ tailWord_838300).sum := by decide
  have hdescent : baseEnd_838300 < baseStart_838300 := by decide
  rcases family_descends (prefixWord ++ tailWord_838300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838321 : List Nat := [1, 2, 2, 6, 2, 1, 2, 1, 1, 4]
def baseStart_838321 : Nat := 118140960795 + 838321 * 2 ^ 59
def prefixEnd_838321 : Nat := 4983230072969 + 3 ^ 40 * 838321 * 2
def baseEnd_838321 : Nat := 286974410505279865954759

theorem tailTrace_838321 : CollatzResearch.WordTrace tailWord_838321 prefixEnd_838321 286974410505279865954759 := by
  unfold tailWord_838321
  simp only [CollatzResearch.WordTrace]
  refine ⟨30576078795913665673258817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20384052530609110448839211 30576078795913665673258817)
  ·
    refine ⟨22932059096935249254944113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30576078795913665673258817 22932059096935249254944113)
    ·
      refine ⟨17199044322701436941208085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22932059096935249254944113 17199044322701436941208085)
      ·
        refine ⟨806205202626629856619129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17199044322701436941208085 806205202626629856619129)
        ·
          refine ⟨604653901969972392464347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 806205202626629856619129 604653901969972392464347)
          ·
            refine ⟨906980852954958588696521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604653901969972392464347 906980852954958588696521)
            ·
              refine ⟨680235639716218941522391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 906980852954958588696521 680235639716218941522391)
              ·
                refine ⟨1020353459574328412283587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 680235639716218941522391 1020353459574328412283587)
                ·
                  refine ⟨1530530189361492618425381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1020353459574328412283587 1530530189361492618425381)
                  ·
                    refine ⟨286974410505279865954759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1530530189361492618425381 286974410505279865954759)
                    ·
                      rfl

theorem cell22_838321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 1, 4].length) (baseStart_838321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838321 prefixEnd_838321 := by exact prefixLift 838321
  have htrace : WordTrace (prefixWord ++ tailWord_838321) baseStart_838321 baseEnd_838321 := by
    simpa [prefixWord, tailWord_838321, baseEnd_838321] using wordTrace_append hprefix tailTrace_838321
  have hstable : (prefixWord ++ tailWord_838321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838321).length < 2 ^ (prefixWord ++ tailWord_838321).sum := by decide
  have hdescent : baseEnd_838321 < baseStart_838321 := by decide
  rcases family_descends (prefixWord ++ tailWord_838321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838450 : List Nat := [3, 2, 1, 1, 3, 1, 1, 4, 2, 4]
def baseStart_838450 : Nat := 118140960795 + 838450 * 2 ^ 59
def prefixEnd_838450 : Nat := 4983230072969 + 3 ^ 40 * 838450 * 2
def baseEnd_838450 : Nat := 287018569841566529479363

theorem tailTrace_838450 : CollatzResearch.WordTrace tailWord_838450 prefixEnd_838450 287018569841566529479363 := by
  unfold tailWord_838450
  simp only [CollatzResearch.WordTrace]
  refine ⟨7645195953111580176176201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20387189208297547136469869 7645195953111580176176201)
  ·
    refine ⟨5733896964833685132132151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7645195953111580176176201 5733896964833685132132151)
    ·
      refine ⟨8600845447250527698198227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5733896964833685132132151 8600845447250527698198227)
      ·
        refine ⟨12901268170875791547297341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8600845447250527698198227 12901268170875791547297341)
        ·
          refine ⟨4837975564078421830236503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12901268170875791547297341 4837975564078421830236503)
          ·
            refine ⟨7256963346117632745354755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4837975564078421830236503 7256963346117632745354755)
            ·
              refine ⟨10885445019176449118032133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7256963346117632745354755 10885445019176449118032133)
              ·
                refine ⟨2041020941095584209631025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10885445019176449118032133 2041020941095584209631025)
                ·
                  refine ⟨1530765705821688157223269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2041020941095584209631025 1530765705821688157223269)
                  ·
                    refine ⟨287018569841566529479363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1530765705821688157223269 287018569841566529479363)
                    ·
                      rfl

theorem cell22_838450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_838450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838450 prefixEnd_838450 := by exact prefixLift 838450
  have htrace : WordTrace (prefixWord ++ tailWord_838450) baseStart_838450 baseEnd_838450 := by
    simpa [prefixWord, tailWord_838450, baseEnd_838450] using wordTrace_append hprefix tailTrace_838450
  have hstable : (prefixWord ++ tailWord_838450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838450).length < 2 ^ (prefixWord ++ tailWord_838450).sum := by decide
  have hdescent : baseEnd_838450 < baseStart_838450 := by decide
  rcases family_descends (prefixWord ++ tailWord_838450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838480 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 5, 3]
def baseStart_838480 : Nat := 118140960795 + 838480 * 2 ^ 59
def prefixEnd_838480 : Nat := 4983230072969 + 3 ^ 40 * 838480 * 2
def baseEnd_838480 : Nat := 287028839454656451229271

theorem tailTrace_838480 : CollatzResearch.WordTrace tailWord_838480 prefixEnd_838480 287028839454656451229271 := by
  unfold tailWord_838480
  simp only [CollatzResearch.WordTrace]
  refine ⟨15290939001168817914148447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20387918668225090552197929 15290939001168817914148447)
  ·
    refine ⟨22936408501753226871222671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15290939001168817914148447 22936408501753226871222671)
    ·
      refine ⟨34404612752629840306834007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22936408501753226871222671 34404612752629840306834007)
      ·
        refine ⟨51606919128944760460251011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34404612752629840306834007 51606919128944760460251011)
        ·
          refine ⟨77410378693417140690376517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51606919128944760460251011 77410378693417140690376517)
          ·
            refine ⟨14514446005015713879445597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77410378693417140690376517 14514446005015713879445597)
            ·
              refine ⟨5442917251880892704792099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14514446005015713879445597 5442917251880892704792099)
              ·
                refine ⟨8164375877821339057188149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5442917251880892704792099 8164375877821339057188149)
                ·
                  refine ⟨765410238545750536611389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8164375877821339057188149 765410238545750536611389)
                  ·
                    refine ⟨287028839454656451229271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 765410238545750536611389 287028839454656451229271)
                    ·
                      rfl

theorem cell22_838480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 5, 3].length) (baseStart_838480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838480 prefixEnd_838480 := by exact prefixLift 838480
  have htrace : WordTrace (prefixWord ++ tailWord_838480) baseStart_838480 baseEnd_838480 := by
    simpa [prefixWord, tailWord_838480, baseEnd_838480] using wordTrace_append hprefix tailTrace_838480
  have hstable : (prefixWord ++ tailWord_838480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838480).length < 2 ^ (prefixWord ++ tailWord_838480).sum := by decide
  have hdescent : baseEnd_838480 < baseStart_838480 := by decide
  rcases family_descends (prefixWord ++ tailWord_838480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838484 : List Nat := [2, 4, 1, 1, 4, 2, 1, 1, 2, 4]
def baseStart_838484 : Nat := 118140960795 + 838484 * 2 ^ 59
def prefixEnd_838484 : Nat := 4983230072969 + 3 ^ 40 * 838484 * 2
def baseEnd_838484 : Nat := 287030208736401774129259

theorem tailTrace_838484 : CollatzResearch.WordTrace tailWord_838484 prefixEnd_838484 287030208736401774129259 := by
  unfold tailWord_838484
  simp only [CollatzResearch.WordTrace]
  refine ⟨15291011947161572255721253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20388015929548763007628337 15291011947161572255721253)
  ·
    refine ⟨2867064740092794797947735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15291011947161572255721253 2867064740092794797947735)
    ·
      refine ⟨4300597110139192196921603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2867064740092794797947735 4300597110139192196921603)
      ·
        refine ⟨6450895665208788295382405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4300597110139192196921603 6450895665208788295382405)
        ·
          refine ⟨1209542937226647805384201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6450895665208788295382405 1209542937226647805384201)
          ·
            refine ⟨907157202919985854038151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1209542937226647805384201 907157202919985854038151)
            ·
              refine ⟨1360735804379978781057227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 907157202919985854038151 1360735804379978781057227)
              ·
                refine ⟨2041103706569968171585841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1360735804379978781057227 2041103706569968171585841)
                ·
                  refine ⟨1530827779927476128689381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2041103706569968171585841 1530827779927476128689381)
                  ·
                    refine ⟨287030208736401774129259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1530827779927476128689381 287030208736401774129259)
                    ·
                      rfl

theorem cell22_838484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_838484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838484 prefixEnd_838484 := by exact prefixLift 838484
  have htrace : WordTrace (prefixWord ++ tailWord_838484) baseStart_838484 baseEnd_838484 := by
    simpa [prefixWord, tailWord_838484, baseEnd_838484] using wordTrace_append hprefix tailTrace_838484
  have hstable : (prefixWord ++ tailWord_838484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838484).length < 2 ^ (prefixWord ++ tailWord_838484).sum := by decide
  have hdescent : baseEnd_838484 < baseStart_838484 := by decide
  rcases family_descends (prefixWord ++ tailWord_838484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838514 : List Nat := [3, 2, 1, 2, 1, 1, 4, 4, 1, 3]
def baseStart_838514 : Nat := 118140960795 + 838514 * 2 ^ 59
def prefixEnd_838514 : Nat := 4983230072969 + 3 ^ 40 * 838514 * 2
def baseEnd_838514 : Nat := 287040478349491695879167

theorem tailTrace_838514 : CollatzResearch.WordTrace tailWord_838514 prefixEnd_838514 287040478349491695879167 := by
  unfold tailWord_838514
  simp only [CollatzResearch.WordTrace]
  refine ⟨7645779521053614908758649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20388745389476306423356397 7645779521053614908758649)
  ·
    refine ⟨5734334640790211181568987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7645779521053614908758649 5734334640790211181568987)
    ·
      refine ⟨8601501961185316772353481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5734334640790211181568987 8601501961185316772353481)
      ·
        refine ⟨6451126470888987579265111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8601501961185316772353481 6451126470888987579265111)
        ·
          refine ⟨9676689706333481368897667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6451126470888987579265111 9676689706333481368897667)
          ·
            refine ⟨14515034559500222053346501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9676689706333481368897667 14515034559500222053346501)
            ·
              refine ⟨2721568979906291635002469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14515034559500222053346501 2721568979906291635002469)
              ·
                refine ⟨510294183732429681562963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2721568979906291635002469 510294183732429681562963)
                ·
                  refine ⟨765441275598644522344445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 510294183732429681562963 765441275598644522344445)
                  ·
                    refine ⟨287040478349491695879167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 765441275598644522344445 287040478349491695879167)
                    ·
                      rfl

theorem cell22_838514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_838514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838514 prefixEnd_838514 := by exact prefixLift 838514
  have htrace : WordTrace (prefixWord ++ tailWord_838514) baseStart_838514 baseEnd_838514 := by
    simpa [prefixWord, tailWord_838514, baseEnd_838514] using wordTrace_append hprefix tailTrace_838514
  have hstable : (prefixWord ++ tailWord_838514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838514).length < 2 ^ (prefixWord ++ tailWord_838514).sum := by decide
  have hdescent : baseEnd_838514 < baseStart_838514 := by decide
  rcases family_descends (prefixWord ++ tailWord_838514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838525 : List Nat := [1, 4, 1, 1, 2, 1, 4, 1, 2, 5]
def baseStart_838525 : Nat := 118140960795 + 838525 * 2 ^ 59
def prefixEnd_838525 : Nat := 4983230072969 + 3 ^ 40 * 838525 * 2
def baseEnd_838525 : Nat := 287044243874291333854133

theorem tailTrace_838525 : CollatzResearch.WordTrace tailWord_838525 prefixEnd_838525 287044243874291333854133 := by
  unfold tailWord_838525
  simp only [CollatzResearch.WordTrace]
  refine ⟨30583519287174608513685029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20389012858116405675790019 30583519287174608513685029)
  ·
    refine ⟨5734409866345239096315943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30583519287174608513685029 5734409866345239096315943)
    ·
      refine ⟨8601614799517858644473915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5734409866345239096315943 8601614799517858644473915)
      ·
        refine ⟨12902422199276787966710873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8601614799517858644473915 12902422199276787966710873)
        ·
          refine ⟨9676816649457590975033155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12902422199276787966710873 9676816649457590975033155)
          ·
            refine ⟨14515224974186386462549733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9676816649457590975033155 14515224974186386462549733)
            ·
              refine ⟨2721604682659947461728075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14515224974186386462549733 2721604682659947461728075)
              ·
                refine ⟨4082407023989921192592113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2721604682659947461728075 4082407023989921192592113)
                ·
                  refine ⟨3061805267992440894444085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4082407023989921192592113 3061805267992440894444085)
                  ·
                    refine ⟨287044243874291333854133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3061805267992440894444085 287044243874291333854133)
                    ·
                      rfl

theorem cell22_838525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_838525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838525 prefixEnd_838525 := by exact prefixLift 838525
  have htrace : WordTrace (prefixWord ++ tailWord_838525) baseStart_838525 baseEnd_838525 := by
    simpa [prefixWord, tailWord_838525, baseEnd_838525] using wordTrace_append hprefix tailTrace_838525
  have hstable : (prefixWord ++ tailWord_838525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838525).length < 2 ^ (prefixWord ++ tailWord_838525).sum := by decide
  have hdescent : baseEnd_838525 < baseStart_838525 := by decide
  rcases family_descends (prefixWord ++ tailWord_838525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838540 : List Nat := [2, 2, 1, 2, 1, 2, 2, 3, 3, 4]
def baseStart_838540 : Nat := 118140960795 + 838540 * 2 ^ 59
def prefixEnd_838540 : Nat := 4983230072969 + 3 ^ 40 * 838540 * 2
def baseEnd_838540 : Nat := 287049378680836294729087

theorem tailTrace_838540 : CollatzResearch.WordTrace tailWord_838540 prefixEnd_838540 287049378680836294729087 := by
  unfold tailWord_838540
  simp only [CollatzResearch.WordTrace]
  refine ⟨15292033191060133037740537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20389377588080177383654049 15292033191060133037740537)
  ·
    refine ⟨11469024893295099778305403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15292033191060133037740537 11469024893295099778305403)
    ·
      refine ⟨17203537339942649667458105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11469024893295099778305403 17203537339942649667458105)
      ·
        refine ⟨12902653004956987250593579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17203537339942649667458105 12902653004956987250593579)
        ·
          refine ⟨19353979507435480875890369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12902653004956987250593579 19353979507435480875890369)
          ·
            refine ⟨14515484630576610656917777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19353979507435480875890369 14515484630576610656917777)
            ·
              refine ⟨10886613472932457992688333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14515484630576610656917777 10886613472932457992688333)
              ·
                refine ⟨4082480052349671747258125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10886613472932457992688333 4082480052349671747258125)
                ·
                  refine ⟨1530930019631126905221797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4082480052349671747258125 1530930019631126905221797)
                  ·
                    refine ⟨287049378680836294729087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1530930019631126905221797 287049378680836294729087)
                    ·
                      rfl

theorem cell22_838540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_838540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838540 prefixEnd_838540 := by exact prefixLift 838540
  have htrace : WordTrace (prefixWord ++ tailWord_838540) baseStart_838540 baseEnd_838540 := by
    simpa [prefixWord, tailWord_838540, baseEnd_838540] using wordTrace_append hprefix tailTrace_838540
  have hstable : (prefixWord ++ tailWord_838540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838540).length < 2 ^ (prefixWord ++ tailWord_838540).sum := by decide
  have hdescent : baseEnd_838540 < baseStart_838540 := by decide
  rcases family_descends (prefixWord ++ tailWord_838540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838557 : List Nat := [1, 4, 2, 1, 2, 1, 1, 5, 1, 4]
def baseStart_838557 : Nat := 118140960795 + 838557 * 2 ^ 59
def prefixEnd_838557 : Nat := 4983230072969 + 3 ^ 40 * 838557 * 2
def baseEnd_838557 : Nat := 287055198128253917054035

theorem tailTrace_838557 : CollatzResearch.WordTrace tailWord_838557 prefixEnd_838557 287055198128253917054035 := by
  unfold tailWord_838557
  simp only [CollatzResearch.WordTrace]
  refine ⟨30584686423058677978849925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20389790948705785319233283 30584686423058677978849925)
  ·
    refine ⟨5734628704323502121034361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30584686423058677978849925 5734628704323502121034361)
    ·
      refine ⟨4300971528242626590775771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5734628704323502121034361 4300971528242626590775771)
      ·
        refine ⟨6451457292363939886163657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4300971528242626590775771 6451457292363939886163657)
        ·
          refine ⟨4838592969272954914622743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6451457292363939886163657 4838592969272954914622743)
          ·
            refine ⟨7257889453909432371934115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4838592969272954914622743 7257889453909432371934115)
            ·
              refine ⟨10886834180864148557901173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7257889453909432371934115 10886834180864148557901173)
              ·
                refine ⟨1020640704456013927303235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10886834180864148557901173 1020640704456013927303235)
                ·
                  refine ⟨1530961056684020890954853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1020640704456013927303235 1530961056684020890954853)
                  ·
                    refine ⟨287055198128253917054035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1530961056684020890954853 287055198128253917054035)
                    ·
                      rfl

theorem cell22_838557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_838557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838557 prefixEnd_838557 := by exact prefixLift 838557
  have htrace : WordTrace (prefixWord ++ tailWord_838557) baseStart_838557 baseEnd_838557 := by
    simpa [prefixWord, tailWord_838557, baseEnd_838557] using wordTrace_append hprefix tailTrace_838557
  have hstable : (prefixWord ++ tailWord_838557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838557).length < 2 ^ (prefixWord ++ tailWord_838557).sum := by decide
  have hdescent : baseEnd_838557 < baseStart_838557 := by decide
  rcases family_descends (prefixWord ++ tailWord_838557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838621 : List Nat := [1, 4, 3, 1, 2, 2, 2, 2, 2, 3]
def baseStart_838621 : Nat := 118140960795 + 838621 * 2 ^ 59
def prefixEnd_838621 : Nat := 4983230072969 + 3 ^ 40 * 838621 * 2
def baseEnd_838621 : Nat := 287077106636179083453839

theorem tailTrace_838621 : CollatzResearch.WordTrace tailWord_838621 prefixEnd_838621 287077106636179083453839 := by
  unfold tailWord_838621
  simp only [CollatzResearch.WordTrace]
  refine ⟨30587020694826816909179717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20391347129884544606119811 30587020694826816909179717)
  ·
    refine ⟨5735066380280028170471197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30587020694826816909179717 5735066380280028170471197)
    ·
      refine ⟨2150649892605010563926699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5735066380280028170471197 2150649892605010563926699)
      ·
        refine ⟨3225974838907515845890049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2150649892605010563926699 3225974838907515845890049)
        ·
          refine ⟨2419481129180636884417537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3225974838907515845890049 2419481129180636884417537)
          ·
            refine ⟨1814610846885477663313153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2419481129180636884417537 1814610846885477663313153)
            ·
              refine ⟨1360958135164108247484865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1814610846885477663313153 1360958135164108247484865)
              ·
                refine ⟨1020718601373081185613649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1360958135164108247484865 1020718601373081185613649)
                ·
                  refine ⟨765538951029810889210237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1020718601373081185613649 765538951029810889210237)
                  ·
                    refine ⟨287077106636179083453839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 765538951029810889210237 287077106636179083453839)
                    ·
                      rfl

theorem cell22_838621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_838621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838621 prefixEnd_838621 := by exact prefixLift 838621
  have htrace : WordTrace (prefixWord ++ tailWord_838621) baseStart_838621 baseEnd_838621 := by
    simpa [prefixWord, tailWord_838621, baseEnd_838621] using wordTrace_append hprefix tailTrace_838621
  have hstable : (prefixWord ++ tailWord_838621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838621).length < 2 ^ (prefixWord ++ tailWord_838621).sum := by decide
  have hdescent : baseEnd_838621 < baseStart_838621 := by decide
  rcases family_descends (prefixWord ++ tailWord_838621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838623 : List Nat := [1, 1, 2, 3, 6, 1, 2, 2, 4]
def baseStart_838623 : Nat := 118140960795 + 838623 * 2 ^ 59
def prefixEnd_838623 : Nat := 4983230072969 + 3 ^ 40 * 838623 * 2
def baseEnd_838623 : Nat := 95692597092350581634611

theorem tailTrace_838623 : CollatzResearch.WordTrace tailWord_838623 prefixEnd_838623 95692597092350581634611 := by
  unfold tailWord_838623
  simp only [CollatzResearch.WordTrace]
  refine ⟨30587093640819571250752523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20391395760546380833835015 30587093640819571250752523)
  ·
    refine ⟨45880640461229356876128785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30587093640819571250752523 45880640461229356876128785)
    ·
      refine ⟨34410480345922017657096589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45880640461229356876128785 34410480345922017657096589)
      ·
        refine ⟨12903930129720756621411221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34410480345922017657096589 12903930129720756621411221)
        ·
          refine ⟨604871724830660466628651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12903930129720756621411221 604871724830660466628651)
          ·
            refine ⟨907307587245990699942977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604871724830660466628651 907307587245990699942977)
            ·
              refine ⟨680480690434493024957233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 907307587245990699942977 680480690434493024957233)
              ·
                refine ⟨510360517825869768717925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 680480690434493024957233 510360517825869768717925)
                ·
                  refine ⟨95692597092350581634611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 510360517825869768717925 95692597092350581634611)
                  ·
                    rfl

theorem cell22_838623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2, 4].length) (baseStart_838623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838623 prefixEnd_838623 := by exact prefixLift 838623
  have htrace : WordTrace (prefixWord ++ tailWord_838623) baseStart_838623 baseEnd_838623 := by
    simpa [prefixWord, tailWord_838623, baseEnd_838623] using wordTrace_append hprefix tailTrace_838623
  have hstable : (prefixWord ++ tailWord_838623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838623).length < 2 ^ (prefixWord ++ tailWord_838623).sum := by decide
  have hdescent : baseEnd_838623 < baseStart_838623 := by decide
  rcases family_descends (prefixWord ++ tailWord_838623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838666 : List Nat := [3, 1, 2, 2, 3, 1, 1, 5, 1, 3]
def baseStart_838666 : Nat := 118140960795 + 838666 * 2 ^ 59
def prefixEnd_838666 : Nat := 4983230072969 + 3 ^ 40 * 838666 * 2
def baseEnd_838666 : Nat := 287092511055813966078701

theorem tailTrace_838666 : CollatzResearch.WordTrace tailWord_838666 prefixEnd_838666 287092511055813966078701 := by
  unfold tailWord_838666
  simp only [CollatzResearch.WordTrace]
  refine ⟨7647165494915947398641963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20392441319775859729711901 7647165494915947398641963)
  ·
    refine ⟨11470748242373921097962945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7647165494915947398641963 11470748242373921097962945)
    ·
      refine ⟨8603061181780440823472209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11470748242373921097962945 8603061181780440823472209)
      ·
        refine ⟨6452295886335330617604157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8603061181780440823472209 6452295886335330617604157)
        ·
          refine ⟨2419610957375748981601559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6452295886335330617604157 2419610957375748981601559)
          ·
            refine ⟨3629416436063623472402339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2419610957375748981601559 3629416436063623472402339)
            ·
              refine ⟨5444124654095435208603509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3629416436063623472402339 5444124654095435208603509)
              ·
                refine ⟨510386686321447050806579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5444124654095435208603509 510386686321447050806579)
                ·
                  refine ⟨765580029482170576209869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 510386686321447050806579 765580029482170576209869)
                  ·
                    refine ⟨287092511055813966078701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 765580029482170576209869 287092511055813966078701)
                    ·
                      rfl

theorem cell22_838666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_838666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838666 prefixEnd_838666 := by exact prefixLift 838666
  have htrace : WordTrace (prefixWord ++ tailWord_838666) baseStart_838666 baseEnd_838666 := by
    simpa [prefixWord, tailWord_838666, baseEnd_838666] using wordTrace_append hprefix tailTrace_838666
  have hstable : (prefixWord ++ tailWord_838666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838666).length < 2 ^ (prefixWord ++ tailWord_838666).sum := by decide
  have hdescent : baseEnd_838666 < baseStart_838666 := by decide
  rcases family_descends (prefixWord ++ tailWord_838666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838677 : List Nat := [1, 3, 2, 1, 4, 1, 1, 2, 2, 5]
def baseStart_838677 : Nat := 118140960795 + 838677 * 2 ^ 59
def prefixEnd_838677 : Nat := 4983230072969 + 3 ^ 40 * 838677 * 2
def baseEnd_838677 : Nat := 287096276580613604053667

theorem tailTrace_838677 : CollatzResearch.WordTrace tailWord_838677 prefixEnd_838677 287096276580613604053667 := by
  unfold tailWord_838677
  simp only [CollatzResearch.WordTrace]
  refine ⟨30589063182623938473218285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20392708788415958982145523 30589063182623938473218285)
  ·
    refine ⟨11470898693483976927456857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30589063182623938473218285 11470898693483976927456857)
    ·
      refine ⟨8603174020112982695592643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11470898693483976927456857 8603174020112982695592643)
      ·
        refine ⟨12904761030169474043388965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8603174020112982695592643 12904761030169474043388965)
        ·
          refine ⟨2419642693156776383135431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12904761030169474043388965 2419642693156776383135431)
          ·
            refine ⟨3629464039735164574703147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2419642693156776383135431 3629464039735164574703147)
            ·
              refine ⟨5444196059602746862054721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3629464039735164574703147 5444196059602746862054721)
              ·
                refine ⟨4083147044702060146541041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5444196059602746862054721 4083147044702060146541041)
                ·
                  refine ⟨3062360283526545109905781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4083147044702060146541041 3062360283526545109905781)
                  ·
                    refine ⟨287096276580613604053667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3062360283526545109905781 287096276580613604053667)
                    ·
                      rfl

theorem cell22_838677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_838677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838677 prefixEnd_838677 := by exact prefixLift 838677
  have htrace : WordTrace (prefixWord ++ tailWord_838677) baseStart_838677 baseEnd_838677 := by
    simpa [prefixWord, tailWord_838677, baseEnd_838677] using wordTrace_append hprefix tailTrace_838677
  have hstable : (prefixWord ++ tailWord_838677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838677).length < 2 ^ (prefixWord ++ tailWord_838677).sum := by decide
  have hdescent : baseEnd_838677 < baseStart_838677 := by decide
  rcases family_descends (prefixWord ++ tailWord_838677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838679 : List Nat := [1, 1, 3, 5, 1, 1, 3, 2, 5]
def baseStart_838679 : Nat := 118140960795 + 838679 * 2 ^ 59
def prefixEnd_838679 : Nat := 4983230072969 + 3 ^ 40 * 838679 * 2
def baseEnd_838679 : Nat := 95698987073828755167887

theorem tailTrace_838679 : CollatzResearch.WordTrace tailWord_838679 prefixEnd_838679 95698987073828755167887 := by
  unfold tailWord_838679
  simp only [CollatzResearch.WordTrace]
  refine ⟨30589136128616692814791091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20392757419077795209860727 30589136128616692814791091)
  ·
    refine ⟨45883704192925039222186637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30589136128616692814791091 45883704192925039222186637)
    ·
      refine ⟨17206389072346889708319989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45883704192925039222186637 17206389072346889708319989)
      ·
        refine ⟨1613098975532520910154999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17206389072346889708319989 1613098975532520910154999)
        ·
          refine ⟨2419648463298781365232499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1613098975532520910154999 2419648463298781365232499)
          ·
            refine ⟨3629472694948172047848749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2419648463298781365232499 3629472694948172047848749)
            ·
              refine ⟨1361052260605564517943281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3629472694948172047848749 1361052260605564517943281)
              ·
                refine ⟨1020789195454173388457461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1361052260605564517943281 1020789195454173388457461)
                ·
                  refine ⟨95698987073828755167887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1020789195454173388457461 95698987073828755167887)
                  ·
                    rfl

theorem cell22_838679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 5].length) (baseStart_838679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838679 prefixEnd_838679 := by exact prefixLift 838679
  have htrace : WordTrace (prefixWord ++ tailWord_838679) baseStart_838679 baseEnd_838679 := by
    simpa [prefixWord, tailWord_838679, baseEnd_838679] using wordTrace_append hprefix tailTrace_838679
  have hstable : (prefixWord ++ tailWord_838679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838679).length < 2 ^ (prefixWord ++ tailWord_838679).sum := by decide
  have hdescent : baseEnd_838679 < baseStart_838679 := by decide
  rcases family_descends (prefixWord ++ tailWord_838679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838737 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 4, 4]
def baseStart_838737 : Nat := 118140960795 + 838737 * 2 ^ 59
def prefixEnd_838737 : Nat := 4983230072969 + 3 ^ 40 * 838737 * 2
def baseEnd_838737 : Nat := 287116815806793447553483

theorem tailTrace_838737 : CollatzResearch.WordTrace tailWord_838737 prefixEnd_838737 287116815806793447553483 := by
  unfold tailWord_838737
  simp only [CollatzResearch.WordTrace]
  refine ⟨30591251562406568720402465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20394167708271045813601643 30591251562406568720402465)
  ·
    refine ⟨22943438671804926540301849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30591251562406568720402465 22943438671804926540301849)
    ·
      refine ⟨17207579003853694905226387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22943438671804926540301849 17207579003853694905226387)
      ·
        refine ⟨25811368505780542357839581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17207579003853694905226387 25811368505780542357839581)
        ·
          refine ⟨9679263189667703384189843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25811368505780542357839581 9679263189667703384189843)
          ·
            refine ⟨14518894784501555076284765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9679263189667703384189843 14518894784501555076284765)
            ·
              refine ⟨5444585544188083153606787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14518894784501555076284765 5444585544188083153606787)
              ·
                refine ⟨8166878316282124730410181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5444585544188083153606787 8166878316282124730410181)
                ·
                  refine ⟨1531289684302898386951909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8166878316282124730410181 1531289684302898386951909)
                  ·
                    refine ⟨287116815806793447553483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1531289684302898386951909 287116815806793447553483)
                    ·
                      rfl

theorem cell22_838737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_838737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838737 prefixEnd_838737 := by exact prefixLift 838737
  have htrace : WordTrace (prefixWord ++ tailWord_838737) baseStart_838737 baseEnd_838737 := by
    simpa [prefixWord, tailWord_838737, baseEnd_838737] using wordTrace_append hprefix tailTrace_838737
  have hstable : (prefixWord ++ tailWord_838737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838737).length < 2 ^ (prefixWord ++ tailWord_838737).sum := by decide
  have hdescent : baseEnd_838737 < baseStart_838737 := by decide
  rcases family_descends (prefixWord ++ tailWord_838737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838741 : List Nat := [1, 3, 2, 2, 1, 2, 5, 2, 4]
def baseStart_838741 : Nat := 118140960795 + 838741 * 2 ^ 59
def prefixEnd_838741 : Nat := 4983230072969 + 3 ^ 40 * 838741 * 2
def baseEnd_838741 : Nat := 95706061696179590151157

theorem tailTrace_838741 : CollatzResearch.WordTrace tailWord_838741 prefixEnd_838741 95706061696179590151157 := by
  unfold tailWord_838741
  simp only [CollatzResearch.WordTrace]
  refine ⟨30591397454392077403548077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20394264969594718269032051 30591397454392077403548077)
  ·
    refine ⟨11471774045397029026330529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30591397454392077403548077 11471774045397029026330529)
    ·
      refine ⟨8603830534047771769747897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11471774045397029026330529 8603830534047771769747897)
      ·
        refine ⟨6452872900535828827310923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8603830534047771769747897 6452872900535828827310923)
        ·
          refine ⟨9679309350803743240966385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6452872900535828827310923 9679309350803743240966385)
          ·
            refine ⟨7259482013102807430724789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9679309350803743240966385 7259482013102807430724789)
            ·
              refine ⟨680576438728388196630449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7259482013102807430724789 680576438728388196630449)
              ·
                refine ⟨510432329046291147472837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 680576438728388196630449 510432329046291147472837)
                ·
                  refine ⟨95706061696179590151157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 510432329046291147472837 95706061696179590151157)
                  ·
                    rfl

theorem cell22_838741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2, 4].length) (baseStart_838741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838741 prefixEnd_838741 := by exact prefixLift 838741
  have htrace : WordTrace (prefixWord ++ tailWord_838741) baseStart_838741 baseEnd_838741 := by
    simpa [prefixWord, tailWord_838741, baseEnd_838741] using wordTrace_append hprefix tailTrace_838741
  have hstable : (prefixWord ++ tailWord_838741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838741).length < 2 ^ (prefixWord ++ tailWord_838741).sum := by decide
  have hdescent : baseEnd_838741 < baseStart_838741 := by decide
  rcases family_descends (prefixWord ++ tailWord_838741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838752 : List Nat := [2, 1, 1, 3, 2, 2, 4, 7]
def baseStart_838752 : Nat := 118140960795 + 838752 * 2 ^ 59
def prefixEnd_838752 : Nat := 4983230072969 + 3 ^ 40 * 838752 * 2
def baseEnd_838752 : Nat := 31902438957037600936493

theorem tailTrace_838752 : CollatzResearch.WordTrace tailWord_838752 prefixEnd_838752 31902438957037600936493 := by
  unfold tailWord_838752
  simp only [CollatzResearch.WordTrace]
  refine ⟨15295899328676113141099255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20394532438234817521465673 15295899328676113141099255)
  ·
    refine ⟨22943848993014169711648883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15295899328676113141099255 22943848993014169711648883)
    ·
      refine ⟨34415773489521254567473325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22943848993014169711648883 34415773489521254567473325)
      ·
        refine ⟨12905915058570470462802497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34415773489521254567473325 12905915058570470462802497)
        ·
          refine ⟨9679436293927852847101873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12905915058570470462802497 9679436293927852847101873)
          ·
            refine ⟨7259577220445889635326405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9679436293927852847101873 7259577220445889635326405)
            ·
              refine ⟨1361170728833604306623701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7259577220445889635326405 1361170728833604306623701)
              ·
                refine ⟨31902438957037600936493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1361170728833604306623701 31902438957037600936493)
                ·
                  rfl

theorem cell22_838752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 7].length) (baseStart_838752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838752 prefixEnd_838752 := by exact prefixLift 838752
  have htrace : WordTrace (prefixWord ++ tailWord_838752) baseStart_838752 baseEnd_838752 := by
    simpa [prefixWord, tailWord_838752, baseEnd_838752] using wordTrace_append hprefix tailTrace_838752
  have hstable : (prefixWord ++ tailWord_838752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838752).length < 2 ^ (prefixWord ++ tailWord_838752).sum := by decide
  have hdescent : baseEnd_838752 < baseStart_838752 := by decide
  rcases family_descends (prefixWord ++ tailWord_838752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838760 : List Nat := [2, 1, 4, 4, 2, 1, 1, 2, 1, 4]
def baseStart_838760 : Nat := 118140960795 + 838760 * 2 ^ 59
def prefixEnd_838760 : Nat := 4983230072969 + 3 ^ 40 * 838760 * 2
def baseEnd_838760 : Nat := 287124689176829054228413

theorem tailTrace_838760 : CollatzResearch.WordTrace tailWord_838760 prefixEnd_838760 287124689176829054228413 := by
  unfold tailWord_838760
  simp only [CollatzResearch.WordTrace]
  refine ⟨15296045220661621824244867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20394726960882162432326489 15296045220661621824244867)
  ·
    refine ⟨22944067830992432736367301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15296045220661621824244867 22944067830992432736367301)
    ·
      refine ⟨4302012718311081138068869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22944067830992432736367301 4302012718311081138068869)
      ·
        refine ⟨806627384683327713387913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4302012718311081138068869 806627384683327713387913)
        ·
          refine ⟨604970538512495785040935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 806627384683327713387913 604970538512495785040935)
          ·
            refine ⟨907455807768743677561403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604970538512495785040935 907455807768743677561403)
            ·
              refine ⟨1361183711653115516342105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 907455807768743677561403 1361183711653115516342105)
              ·
                refine ⟨1020887783739836637256579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1361183711653115516342105 1020887783739836637256579)
                ·
                  refine ⟨1531331675609754955884869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1020887783739836637256579 1531331675609754955884869)
                  ·
                    refine ⟨287124689176829054228413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1531331675609754955884869 287124689176829054228413)
                    ·
                      rfl

theorem cell22_838760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_838760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838760 prefixEnd_838760 := by exact prefixLift 838760
  have htrace : WordTrace (prefixWord ++ tailWord_838760) baseStart_838760 baseEnd_838760 := by
    simpa [prefixWord, tailWord_838760, baseEnd_838760] using wordTrace_append hprefix tailTrace_838760
  have hstable : (prefixWord ++ tailWord_838760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838760).length < 2 ^ (prefixWord ++ tailWord_838760).sum := by decide
  have hdescent : baseEnd_838760 < baseStart_838760 := by decide
  rcases family_descends (prefixWord ++ tailWord_838760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838818 : List Nat := [3, 3, 1, 3, 2, 1, 1, 2, 3, 3]
def baseStart_838818 : Nat := 118140960795 + 838818 * 2 ^ 59
def prefixEnd_838818 : Nat := 4983230072969 + 3 ^ 40 * 838818 * 2
def baseEnd_838818 : Nat := 287144543762136236278235

theorem tailTrace_838818 : CollatzResearch.WordTrace tailWord_838818 prefixEnd_838818 287144543762136236278235 := by
  unfold tailWord_838818
  simp only [CollatzResearch.WordTrace]
  refine ⟨7648551468778279888525277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20396137250075413036067405 7648551468778279888525277)
  ·
    refine ⟨2868206800791854958196979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7648551468778279888525277 2868206800791854958196979)
    ·
      refine ⟨4302310201187782437295469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2868206800791854958196979 4302310201187782437295469)
      ·
        refine ⟨1613366325445418413985801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4302310201187782437295469 1613366325445418413985801)
        ·
          refine ⟨1210024744084063810489351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1613366325445418413985801 1210024744084063810489351)
          ·
            refine ⟨1815037116126095715734027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1210024744084063810489351 1815037116126095715734027)
            ·
              refine ⟨2722555674189143573601041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1815037116126095715734027 2722555674189143573601041)
              ·
                refine ⟨2041916755641857680200781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2722555674189143573601041 2041916755641857680200781)
                ·
                  refine ⟨765718783365696630075293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2041916755641857680200781 765718783365696630075293)
                  ·
                    refine ⟨287144543762136236278235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 765718783365696630075293 287144543762136236278235)
                    ·
                      rfl

theorem cell22_838818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_838818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838818 prefixEnd_838818 := by exact prefixLift 838818
  have htrace : WordTrace (prefixWord ++ tailWord_838818) baseStart_838818 baseEnd_838818 := by
    simpa [prefixWord, tailWord_838818, baseEnd_838818] using wordTrace_append hprefix tailTrace_838818
  have hstable : (prefixWord ++ tailWord_838818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838818).length < 2 ^ (prefixWord ++ tailWord_838818).sum := by decide
  have hdescent : baseEnd_838818 < baseStart_838818 := by decide
  rcases family_descends (prefixWord ++ tailWord_838818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838842 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 10]
def baseStart_838842 : Nat := 118140960795 + 838842 * 2 ^ 59
def prefixEnd_838842 : Nat := 4983230072969 + 3 ^ 40 * 838842 * 2
def baseEnd_838842 : Nat := 95717586484202724559387

theorem tailTrace_838842 : CollatzResearch.WordTrace tailWord_838842 prefixEnd_838842 95717586484202724559387 := by
  unfold tailWord_838842
  simp only [CollatzResearch.WordTrace]
  refine ⟨7648770306756542913243695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20396720818017447768649853 7648770306756542913243695)
  ·
    refine ⟨11473155460134814369865543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7648770306756542913243695 11473155460134814369865543)
    ·
      refine ⟨17209733190202221554798315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11473155460134814369865543 17209733190202221554798315)
      ·
        refine ⟨25814599785303332332197473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17209733190202221554798315 25814599785303332332197473)
        ·
          refine ⟨19360949838977499249148105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25814599785303332332197473 19360949838977499249148105)
          ·
            refine ⟨14520712379233124436861079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19360949838977499249148105 14520712379233124436861079)
            ·
              refine ⟨21781068568849686655291619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14520712379233124436861079 21781068568849686655291619)
              ·
                refine ⟨32671602853274529982937429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21781068568849686655291619 32671602853274529982937429)
                ·
                  refine ⟨95717586484202724559387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 32671602853274529982937429 95717586484202724559387)
                  ·
                    rfl

theorem cell22_838842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_838842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838842 prefixEnd_838842 := by exact prefixLift 838842
  have htrace : WordTrace (prefixWord ++ tailWord_838842) baseStart_838842 baseEnd_838842 := by
    simpa [prefixWord, tailWord_838842, baseEnd_838842] using wordTrace_append hprefix tailTrace_838842
  have hstable : (prefixWord ++ tailWord_838842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838842).length < 2 ^ (prefixWord ++ tailWord_838842).sum := by decide
  have hdescent : baseEnd_838842 < baseStart_838842 := by decide
  rcases family_descends (prefixWord ++ tailWord_838842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838848 : List Nat := [2, 1, 1, 2, 7, 1, 1, 2, 5]
def baseStart_838848 : Nat := 118140960795 + 838848 * 2 ^ 59
def prefixEnd_838848 : Nat := 4983230072969 + 3 ^ 40 * 838848 * 2
def baseEnd_838848 : Nat := 95718271125075386009381

theorem tailTrace_838848 : CollatzResearch.WordTrace tailWord_838848 prefixEnd_838848 95718271125075386009381 := by
  unfold tailWord_838848
  simp only [CollatzResearch.WordTrace]
  refine ⟨15297650032502217338846599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20396866710002956451795465 15297650032502217338846599)
  ·
    refine ⟨22946475048753326008269899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15297650032502217338846599 22946475048753326008269899)
    ·
      refine ⟨34419712573129989012404849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22946475048753326008269899 34419712573129989012404849)
      ·
        refine ⟨25814784429847491759303637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34419712573129989012404849 25814784429847491759303637)
        ·
          refine ⟨605034010074550588108679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 25814784429847491759303637 605034010074550588108679)
          ·
            refine ⟨907551015111825882163019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605034010074550588108679 907551015111825882163019)
            ·
              refine ⟨1361326522667738823244529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 907551015111825882163019 1361326522667738823244529)
              ·
                refine ⟨1020994892000804117433397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1361326522667738823244529 1020994892000804117433397)
                ·
                  refine ⟨95718271125075386009381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1020994892000804117433397 95718271125075386009381)
                  ·
                    rfl

theorem cell22_838848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 5].length) (baseStart_838848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838848 prefixEnd_838848 := by exact prefixLift 838848
  have htrace : WordTrace (prefixWord ++ tailWord_838848) baseStart_838848 baseEnd_838848 := by
    simpa [prefixWord, tailWord_838848, baseEnd_838848] using wordTrace_append hprefix tailTrace_838848
  have hstable : (prefixWord ++ tailWord_838848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838848).length < 2 ^ (prefixWord ++ tailWord_838848).sum := by decide
  have hdescent : baseEnd_838848 < baseStart_838848 := by decide
  rcases family_descends (prefixWord ++ tailWord_838848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838893 : List Nat := [1, 5, 1, 2, 2, 1, 3, 3, 4]
def baseStart_838893 : Nat := 118140960795 + 838893 * 2 ^ 59
def prefixEnd_838893 : Nat := 4983230072969 + 3 ^ 40 * 838893 * 2
def baseEnd_838893 : Nat := 95723405931620346884335

theorem tailTrace_838893 : CollatzResearch.WordTrace tailWord_838893 prefixEnd_838893 95723405931620346884335 := by
  unfold tailWord_838893
  simp only [CollatzResearch.WordTrace]
  refine ⟨30596941349841407363081333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20397960899894271575387555 30596941349841407363081333)
  ·
    refine ⟨2868463251547631940288875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30596941349841407363081333 2868463251547631940288875)
    ·
      refine ⟨4302694877321447910433313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2868463251547631940288875 4302694877321447910433313)
      ·
        refine ⟨3227021157991085932824985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4302694877321447910433313 3227021157991085932824985)
        ·
          refine ⟨2420265868493314449618739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3227021157991085932824985 2420265868493314449618739)
          ·
            refine ⟨3630398802739971674428109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2420265868493314449618739 3630398802739971674428109)
            ·
              refine ⟨1361399551027489377910541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3630398802739971674428109 1361399551027489377910541)
              ·
                refine ⟨510524831635308516716453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1361399551027489377910541 510524831635308516716453)
                ·
                  refine ⟨95723405931620346884335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 510524831635308516716453 95723405931620346884335)
                  ·
                    rfl

theorem cell22_838893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_838893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838893 prefixEnd_838893 := by exact prefixLift 838893
  have htrace : WordTrace (prefixWord ++ tailWord_838893) baseStart_838893 baseEnd_838893 := by
    simpa [prefixWord, tailWord_838893, baseEnd_838893] using wordTrace_append hprefix tailTrace_838893
  have hstable : (prefixWord ++ tailWord_838893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838893).length < 2 ^ (prefixWord ++ tailWord_838893).sum := by decide
  have hdescent : baseEnd_838893 < baseStart_838893 := by decide
  rcases family_descends (prefixWord ++ tailWord_838893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838910 : List Nat := [4, 2, 2, 1, 1, 3, 3, 2, 4]
def baseStart_838910 : Nat := 118140960795 + 838910 * 2 ^ 59
def prefixEnd_838910 : Nat := 4983230072969 + 3 ^ 40 * 838910 * 2
def baseEnd_838910 : Nat := 95725345747426220992651

theorem tailTrace_838910 : CollatzResearch.WordTrace tailWord_838910 prefixEnd_838910 95725345747426220992651 := by
  unfold tailWord_838910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3824695173847477408306273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20398374260519879510966789 3824695173847477408306273)
  ·
    refine ⟨2868521380385608056229705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3824695173847477408306273 2868521380385608056229705)
    ·
      refine ⟨2151391035289206042172279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2868521380385608056229705 2151391035289206042172279)
      ·
        refine ⟨3227086552933809063258419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2151391035289206042172279 3227086552933809063258419)
        ·
          refine ⟨4840629829400713594887629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3227086552933809063258419 4840629829400713594887629)
          ·
            refine ⟨1815236186025267598082861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4840629829400713594887629 1815236186025267598082861)
            ·
              refine ⟨680713569759475349281073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1815236186025267598082861 680713569759475349281073)
              ·
                refine ⟨510535177319606511960805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 680713569759475349281073 510535177319606511960805)
                ·
                  refine ⟨95725345747426220992651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 510535177319606511960805 95725345747426220992651)
                  ·
                    rfl

theorem cell22_838910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_838910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838910 prefixEnd_838910 := by exact prefixLift 838910
  have htrace : WordTrace (prefixWord ++ tailWord_838910) baseStart_838910 baseEnd_838910 := by
    simpa [prefixWord, tailWord_838910, baseEnd_838910] using wordTrace_append hprefix tailTrace_838910
  have hstable : (prefixWord ++ tailWord_838910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838910).length < 2 ^ (prefixWord ++ tailWord_838910).sum := by decide
  have hdescent : baseEnd_838910 < baseStart_838910 := by decide
  rcases family_descends (prefixWord ++ tailWord_838910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838996 : List Nat := [2, 4, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_838996 : Nat := 118140960795 + 838996 * 2 ^ 59
def prefixEnd_838996 : Nat := 4983230072969 + 3 ^ 40 * 838996 * 2
def baseEnd_838996 : Nat := 287205476799803105327689

theorem tailTrace_838996 : CollatzResearch.WordTrace tailWord_838996 prefixEnd_838996 287205476799803105327689 := by
  unfold tailWord_838996
  simp only [CollatzResearch.WordTrace]
  refine ⟨15300349034234127977040421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20400465378978837302720561 15300349034234127977040421)
  ·
    refine ⟨2868815443918898995695079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15300349034234127977040421 2868815443918898995695079)
    ·
      refine ⟨4303223165878348493542619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2868815443918898995695079 4303223165878348493542619)
      ·
        refine ⟨6454834748817522740313929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4303223165878348493542619 6454834748817522740313929)
        ·
          refine ⟨4841126061613142055235447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6454834748817522740313929 4841126061613142055235447)
          ·
            refine ⟨7261689092419713082853171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4841126061613142055235447 7261689092419713082853171)
            ·
              refine ⟨10892533638629569624279757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7261689092419713082853171 10892533638629569624279757)
              ·
                refine ⟨4084700114486088609104909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10892533638629569624279757 4084700114486088609104909)
                ·
                  refine ⟨1531762542932283228414341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4084700114486088609104909 1531762542932283228414341)
                  ·
                    refine ⟨287205476799803105327689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1531762542932283228414341 287205476799803105327689)
                    ·
                      rfl

theorem cell22_838996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_838996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_838996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_838996 prefixEnd_838996 := by exact prefixLift 838996
  have htrace : WordTrace (prefixWord ++ tailWord_838996) baseStart_838996 baseEnd_838996 := by
    simpa [prefixWord, tailWord_838996, baseEnd_838996] using wordTrace_append hprefix tailTrace_838996
  have hstable : (prefixWord ++ tailWord_838996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838996).length < 2 ^ (prefixWord ++ tailWord_838996).sum := by decide
  have hdescent : baseEnd_838996 < baseStart_838996 := by decide
  rcases family_descends (prefixWord ++ tailWord_838996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839043 : List Nat := [1, 1, 1, 3, 5, 3, 1, 1, 1, 5]
def baseStart_839043 : Nat := 118140960795 + 839043 * 2 ^ 59
def prefixEnd_839043 : Nat := 4983230072969 + 3 ^ 40 * 839043 * 2
def baseEnd_839043 : Nat := 287221565860310649402545

theorem tailTrace_839043 : CollatzResearch.WordTrace tailWord_839043 prefixEnd_839043 287221565860310649402545 := by
  unfold tailWord_839043
  simp only [CollatzResearch.WordTrace]
  refine ⟨30602412299297982981041783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20401608199531988654027855 30602412299297982981041783)
  ·
    refine ⟨45903618448946974471562675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30602412299297982981041783 45903618448946974471562675)
    ·
      refine ⟨68855427673420461707344013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45903618448946974471562675 68855427673420461707344013)
      ·
        refine ⟨25820785377532673140254005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68855427673420461707344013 25820785377532673140254005)
        ·
          refine ⟨2420698629143688106898813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25820785377532673140254005 2420698629143688106898813)
          ·
            refine ⟨907761985928883040087055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2420698629143688106898813 907761985928883040087055)
            ·
              refine ⟨1361642978893324560130583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 907761985928883040087055 1361642978893324560130583)
              ·
                refine ⟨2042464468339986840195875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1361642978893324560130583 2042464468339986840195875)
                ·
                  refine ⟨3063696702509980260293813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2042464468339986840195875 3063696702509980260293813)
                  ·
                    refine ⟨287221565860310649402545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3063696702509980260293813 287221565860310649402545)
                    ·
                      rfl

theorem cell22_839043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 5].length) (baseStart_839043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_839043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_839043 prefixEnd_839043 := by exact prefixLift 839043
  have htrace : WordTrace (prefixWord ++ tailWord_839043) baseStart_839043 baseEnd_839043 := by
    simpa [prefixWord, tailWord_839043, baseEnd_839043] using wordTrace_append hprefix tailTrace_839043
  have hstable : (prefixWord ++ tailWord_839043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839043).length < 2 ^ (prefixWord ++ tailWord_839043).sum := by decide
  have hdescent : baseEnd_839043 < baseStart_839043 := by decide
  rcases family_descends (prefixWord ++ tailWord_839043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839139 : List Nat := [1, 1, 1, 6, 2, 3, 2, 2, 1, 3]
def baseStart_839139 : Nat := 118140960795 + 839139 * 2 ^ 59
def prefixEnd_839139 : Nat := 4983230072969 + 3 ^ 40 * 839139 * 2
def baseEnd_839139 : Nat := 287254428622198399002251

theorem tailTrace_839139 : CollatzResearch.WordTrace tailWord_839139 prefixEnd_839139 287254428622198399002251 := by
  unfold tailWord_839139
  simp only [CollatzResearch.WordTrace]
  refine ⟨30605913706950191376536471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20403942471300127584357647 30605913706950191376536471)
  ·
    refine ⟨45908870560425287064804707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30605913706950191376536471 45908870560425287064804707)
    ·
      refine ⟨68863305840637930597207061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45908870560425287064804707 68863305840637930597207061)
      ·
        refine ⟨3227967461279902996744081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68863305840637930597207061 3227967461279902996744081)
        ·
          refine ⟨2420975595959927247558061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3227967461279902996744081 2420975595959927247558061)
          ·
            refine ⟨907865848484972717834273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2420975595959927247558061 907865848484972717834273)
            ·
              refine ⟨680899386363729538375705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 907865848484972717834273 680899386363729538375705)
              ·
                refine ⟨510674539772797153781779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 680899386363729538375705 510674539772797153781779)
                ·
                  refine ⟨766011809659195730672669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 510674539772797153781779 766011809659195730672669)
                  ·
                    refine ⟨287254428622198399002251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 766011809659195730672669 287254428622198399002251)
                    ·
                      rfl

theorem cell22_839139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2, 1, 3].length) (baseStart_839139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_839139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_839139 prefixEnd_839139 := by exact prefixLift 839139
  have htrace : WordTrace (prefixWord ++ tailWord_839139) baseStart_839139 baseEnd_839139 := by
    simpa [prefixWord, tailWord_839139, baseEnd_839139] using wordTrace_append hprefix tailTrace_839139
  have hstable : (prefixWord ++ tailWord_839139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839139).length < 2 ^ (prefixWord ++ tailWord_839139).sum := by decide
  have hdescent : baseEnd_839139 < baseStart_839139 := by decide
  rcases family_descends (prefixWord ++ tailWord_839139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839178 : List Nat := [3, 1, 2, 2, 2, 2, 2, 2, 1, 5]
def baseStart_839178 : Nat := 118140960795 + 839178 * 2 ^ 59
def prefixEnd_839178 : Nat := 4983230072969 + 3 ^ 40 * 839178 * 2
def baseEnd_839178 : Nat := 287267779119215297277131

theorem tailTrace_839178 : CollatzResearch.WordTrace tailWord_839178 prefixEnd_839178 287267779119215297277131 := by
  unfold tailWord_839178
  simp only [CollatzResearch.WordTrace]
  refine ⟨7651834038452225259301547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20404890769205934024804125 7651834038452225259301547)
  ·
    refine ⟨11477751057678337888952321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7651834038452225259301547 11477751057678337888952321)
    ·
      refine ⟨8608313293258753416714241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11477751057678337888952321 8608313293258753416714241)
      ·
        refine ⟨6456234969944065062535681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8608313293258753416714241 6456234969944065062535681)
        ·
          refine ⟨4842176227458048796901761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6456234969944065062535681 4842176227458048796901761)
          ·
            refine ⟨3631632170593536597676321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4842176227458048796901761 3631632170593536597676321)
            ·
              refine ⟨2723724127945152448257241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3631632170593536597676321 2723724127945152448257241)
              ·
                refine ⟨2042793095958864336192931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2723724127945152448257241 2042793095958864336192931)
                ·
                  refine ⟨3064189643938296504289397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2042793095958864336192931 3064189643938296504289397)
                  ·
                    refine ⟨287267779119215297277131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3064189643938296504289397 287267779119215297277131)
                    ·
                      rfl

theorem cell22_839178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_839178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_839178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_839178 prefixEnd_839178 := by exact prefixLift 839178
  have htrace : WordTrace (prefixWord ++ tailWord_839178) baseStart_839178 baseEnd_839178 := by
    simpa [prefixWord, tailWord_839178, baseEnd_839178] using wordTrace_append hprefix tailTrace_839178
  have hstable : (prefixWord ++ tailWord_839178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839178).length < 2 ^ (prefixWord ++ tailWord_839178).sum := by decide
  have hdescent : baseEnd_839178 < baseStart_839178 := by decide
  rcases family_descends (prefixWord ++ tailWord_839178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839225 : List Nat := [1, 2, 1, 5, 1, 4, 2, 6]
def baseStart_839225 : Nat := 118140960795 + 839225 * 2 ^ 59
def prefixEnd_839225 : Nat := 4983230072969 + 3 ^ 40 * 839225 * 2
def baseEnd_839225 : Nat := 31920429797746982372443

theorem tailTrace_839225 : CollatzResearch.WordTrace tailWord_839225 prefixEnd_839225 31920429797746982372443 := by
  unfold tailWord_839225
  simp only [CollatzResearch.WordTrace]
  refine ⟨30609050384638628064167129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20406033589759085376111419 30609050384638628064167129)
  ·
    refine ⟨22956787788478971048125347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30609050384638628064167129 22956787788478971048125347)
    ·
      refine ⟨34435181682718456572188021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22956787788478971048125347 34435181682718456572188021)
      ·
        refine ⟨3228298282754855303642627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34435181682718456572188021 3228298282754855303642627)
        ·
          refine ⟨4842447424132282955463941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3228298282754855303642627 4842447424132282955463941)
          ·
            refine ⟨907958892024803054149489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4842447424132282955463941 907958892024803054149489)
            ·
              refine ⟨680969169018602290612117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 907958892024803054149489 680969169018602290612117)
              ·
                refine ⟨31920429797746982372443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 680969169018602290612117 31920429797746982372443)
                ·
                  rfl

theorem cell22_839225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 6].length) (baseStart_839225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_839225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_839225 prefixEnd_839225 := by exact prefixLift 839225
  have htrace : WordTrace (prefixWord ++ tailWord_839225) baseStart_839225 baseEnd_839225 := by
    simpa [prefixWord, tailWord_839225, baseEnd_839225] using wordTrace_append hprefix tailTrace_839225
  have hstable : (prefixWord ++ tailWord_839225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839225).length < 2 ^ (prefixWord ++ tailWord_839225).sum := by decide
  have hdescent : baseEnd_839225 < baseStart_839225 := by decide
  rcases family_descends (prefixWord ++ tailWord_839225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839251 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 5, 7]
def baseStart_839251 : Nat := 118140960795 + 839251 * 2 ^ 59
def prefixEnd_839251 : Nat := 4983230072969 + 3 ^ 40 * 839251 * 2
def baseEnd_839251 : Nat := 287292768511067440201907

theorem tailTrace_839251 : CollatzResearch.WordTrace tailWord_839251 prefixEnd_839251 287292768511067440201907 := by
  unfold tailWord_839251
  simp only [CollatzResearch.WordTrace]
  refine ⟨30609998682544434504613607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20406665788362956336409071 30609998682544434504613607)
  ·
    refine ⟨45914998023816651756920411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30609998682544434504613607 45914998023816651756920411)
    ·
      refine ⟨68872497035724977635380617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45914998023816651756920411 68872497035724977635380617)
      ·
        refine ⟨51654372776793733226535463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68872497035724977635380617 51654372776793733226535463)
        ·
          refine ⟨77481559165190599839803195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51654372776793733226535463 77481559165190599839803195)
          ·
            refine ⟨116222338747785899759704793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77481559165190599839803195 116222338747785899759704793)
            ·
              refine ⟨87166754060839424819778595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116222338747785899759704793 87166754060839424819778595)
              ·
                refine ⟨130750131091259137229667893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87166754060839424819778595 130750131091259137229667893)
                ·
                  refine ⟨12257824789805544115281365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130750131091259137229667893 12257824789805544115281365)
                  ·
                    refine ⟨287292768511067440201907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12257824789805544115281365 287292768511067440201907)
                    ·
                      rfl

theorem cell22_839251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 7].length) (baseStart_839251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_839251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_839251 prefixEnd_839251 := by exact prefixLift 839251
  have htrace : WordTrace (prefixWord ++ tailWord_839251) baseStart_839251 baseEnd_839251 := by
    simpa [prefixWord, tailWord_839251, baseEnd_839251] using wordTrace_append hprefix tailTrace_839251
  have hstable : (prefixWord ++ tailWord_839251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839251).length < 2 ^ (prefixWord ++ tailWord_839251).sum := by decide
  have hdescent : baseEnd_839251 < baseStart_839251 := by decide
  rcases family_descends (prefixWord ++ tailWord_839251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839253 : List Nat := [1, 3, 2, 2, 1, 1, 1, 6, 5]
def baseStart_839253 : Nat := 118140960795 + 839253 * 2 ^ 59
def prefixEnd_839253 : Nat := 4983230072969 + 3 ^ 40 * 839253 * 2
def baseEnd_839253 : Nat := 95764484383980033883967

theorem tailTrace_839253 : CollatzResearch.WordTrace tailWord_839253 prefixEnd_839253 95764484383980033883967 := by
  unfold tailWord_839253
  simp only [CollatzResearch.WordTrace]
  refine ⟨30610071628537188846186413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20406714419024792564124275 30610071628537188846186413)
  ·
    refine ⟨11478776860701445817319905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30610071628537188846186413 11478776860701445817319905)
    ·
      refine ⟨8609082645526084362989929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11478776860701445817319905 8609082645526084362989929)
      ·
        refine ⟨6456811984144563272242447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8609082645526084362989929 6456811984144563272242447)
        ·
          refine ⟨9685217976216844908363671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6456811984144563272242447 9685217976216844908363671)
          ·
            refine ⟨14527826964325267362545507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9685217976216844908363671 14527826964325267362545507)
            ·
              refine ⟨21791740446487901043818261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14527826964325267362545507 21791740446487901043818261)
              ·
                refine ⟨1021487833429120361428981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21791740446487901043818261 1021487833429120361428981)
                ·
                  refine ⟨95764484383980033883967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1021487833429120361428981 95764484383980033883967)
                  ·
                    rfl

theorem cell22_839253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 5].length) (baseStart_839253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_839253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_839253 prefixEnd_839253 := by exact prefixLift 839253
  have htrace : WordTrace (prefixWord ++ tailWord_839253) baseStart_839253 baseEnd_839253 := by
    simpa [prefixWord, tailWord_839253, baseEnd_839253] using wordTrace_append hprefix tailTrace_839253
  have hstable : (prefixWord ++ tailWord_839253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839253).length < 2 ^ (prefixWord ++ tailWord_839253).sum := by decide
  have hdescent : baseEnd_839253 < baseStart_839253 := by decide
  rcases family_descends (prefixWord ++ tailWord_839253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839349 : List Nat := [1, 3, 3, 3, 2, 1, 2, 3, 4]
def baseStart_839349 : Nat := 118140960795 + 839349 * 2 ^ 59
def prefixEnd_839349 : Nat := 4983230072969 + 3 ^ 40 * 839349 * 2
def baseEnd_839349 : Nat := 95775438637942617083869

theorem tailTrace_839349 : CollatzResearch.WordTrace tailWord_839349 prefixEnd_839349 95775438637942617083869 := by
  unfold tailWord_839349
  simp only [CollatzResearch.WordTrace]
  refine ⟨30613573036189397241681101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20409048690792931494454067 30613573036189397241681101)
  ·
    refine ⟨11480089888571023965630413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30613573036189397241681101 11480089888571023965630413)
    ·
      refine ⟨4305033708214133987111405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11480089888571023965630413 4305033708214133987111405)
      ·
        refine ⟨1614387640580300245166777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4305033708214133987111405 1614387640580300245166777)
        ·
          refine ⟨1210790730435225183875083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1614387640580300245166777 1210790730435225183875083)
          ·
            refine ⟨1816186095652837775812625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1210790730435225183875083 1816186095652837775812625)
            ·
              refine ⟨1362139571739628331859469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1816186095652837775812625 1362139571739628331859469)
              ·
                refine ⟨510802339402360624447301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1362139571739628331859469 510802339402360624447301)
                ·
                  refine ⟨95775438637942617083869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 510802339402360624447301 95775438637942617083869)
                  ·
                    rfl

theorem cell22_839349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3, 4].length) (baseStart_839349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_839349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_839349 prefixEnd_839349 := by exact prefixLift 839349
  have htrace : WordTrace (prefixWord ++ tailWord_839349) baseStart_839349 baseEnd_839349 := by
    simpa [prefixWord, tailWord_839349, baseEnd_839349] using wordTrace_append hprefix tailTrace_839349
  have hstable : (prefixWord ++ tailWord_839349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839349).length < 2 ^ (prefixWord ++ tailWord_839349).sum := by decide
  have hdescent : baseEnd_839349 < baseStart_839349 := by decide
  rcases family_descends (prefixWord ++ tailWord_839349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839366 : List Nat := [6, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_839366 : Nat := 118140960795 + 839366 * 2 ^ 59
def prefixEnd_839366 : Nat := 4983230072969 + 3 ^ 40 * 839366 * 2
def baseEnd_839366 : Nat := 95777378453748491192185

theorem tailTrace_839366 : CollatzResearch.WordTrace tailWord_839366 prefixEnd_839366 95777378453748491192185 := by
  unfold tailWord_839366
  simp only [CollatzResearch.WordTrace]
  refine ⟨956693533660244035782811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20409462051418539430033301 956693533660244035782811)
  ·
    refine ⟨1435040300490366053674217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 956693533660244035782811 1435040300490366053674217)
    ·
      refine ⟨1076280225367774540255663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1435040300490366053674217 1076280225367774540255663)
      ·
        refine ⟨1614420338051661810383495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1076280225367774540255663 1614420338051661810383495)
        ·
          refine ⟨2421630507077492715575243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1614420338051661810383495 2421630507077492715575243)
          ·
            refine ⟨3632445760616239073362865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2421630507077492715575243 3632445760616239073362865)
            ·
              refine ⟨2724334320462179305022149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3632445760616239073362865 2724334320462179305022149)
              ·
                refine ⟨510812685086658619691653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2724334320462179305022149 510812685086658619691653)
                ·
                  refine ⟨95777378453748491192185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 510812685086658619691653 95777378453748491192185)
                  ·
                    rfl

theorem cell22_839366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_839366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_839366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_839366 prefixEnd_839366 := by exact prefixLift 839366
  have htrace : WordTrace (prefixWord ++ tailWord_839366) baseStart_839366 baseEnd_839366 := by
    simpa [prefixWord, tailWord_839366, baseEnd_839366] using wordTrace_append hprefix tailTrace_839366
  have hstable : (prefixWord ++ tailWord_839366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839366).length < 2 ^ (prefixWord ++ tailWord_839366).sum := by decide
  have hdescent : baseEnd_839366 < baseStart_839366 := by decide
  rcases family_descends (prefixWord ++ tailWord_839366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839403 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 1, 7]
def baseStart_839403 : Nat := 118140960795 + 839403 * 2 ^ 59
def prefixEnd_839403 : Nat := 4983230072969 + 3 ^ 40 * 839403 * 2
def baseEnd_839403 : Nat := 287344801217389710401441

theorem tailTrace_839403 : CollatzResearch.WordTrace tailWord_839403 prefixEnd_839403 287344801217389710401441 := by
  unfold tailWord_839403
  simp only [CollatzResearch.WordTrace]
  refine ⟨30615542577993764464146863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20410361718662509642764575 30615542577993764464146863)
  ·
    refine ⟨45923313866990646696220295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30615542577993764464146863 45923313866990646696220295)
    ·
      refine ⟨68884970800485970044330443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45923313866990646696220295 68884970800485970044330443)
      ·
        refine ⟨103327456200728955066495665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68884970800485970044330443 103327456200728955066495665)
        ·
          refine ⟨77495592150546716299871749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103327456200728955066495665 77495592150546716299871749)
          ·
            refine ⟨14530423528227509306225953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77495592150546716299871749 14530423528227509306225953)
            ·
              refine ⟨10897817646170631979669465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14530423528227509306225953 10897817646170631979669465)
              ·
                refine ⟨8173363234627973984752099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10897817646170631979669465 8173363234627973984752099)
                ·
                  refine ⟨12260044851941960977128149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8173363234627973984752099 12260044851941960977128149)
                  ·
                    refine ⟨287344801217389710401441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12260044851941960977128149 287344801217389710401441)
                    ·
                      rfl

theorem cell22_839403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 7].length) (baseStart_839403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_839403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_839403 prefixEnd_839403 := by exact prefixLift 839403
  have htrace : WordTrace (prefixWord ++ tailWord_839403) baseStart_839403 baseEnd_839403 := by
    simpa [prefixWord, tailWord_839403, baseEnd_839403] using wordTrace_append hprefix tailTrace_839403
  have hstable : (prefixWord ++ tailWord_839403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839403).length < 2 ^ (prefixWord ++ tailWord_839403).sum := by decide
  have hdescent : baseEnd_839403 < baseStart_839403 := by decide
  rcases family_descends (prefixWord ++ tailWord_839403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839405 : List Nat := [1, 5, 1, 2, 1, 2, 1, 2, 7]
def baseStart_839405 : Nat := 118140960795 + 839405 * 2 ^ 59
def prefixEnd_839405 : Nat := 4983230072969 + 3 ^ 40 * 839405 * 2
def baseEnd_839405 : Nat := 95781828619420790617145

theorem tailTrace_839405 : CollatzResearch.WordTrace tailWord_839405 prefixEnd_839405 95781828619420790617145 := by
  unfold tailWord_839405
  simp only [CollatzResearch.WordTrace]
  refine ⟨30615615523986518805719669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20410410349324345870479779 30615615523986518805719669)
  ·
    refine ⟨2870213955373736138036219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30615615523986518805719669 2870213955373736138036219)
    ·
      refine ⟨4305320933060604207054329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2870213955373736138036219 4305320933060604207054329)
      ·
        refine ⟨3228990699795453155290747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4305320933060604207054329 3228990699795453155290747)
        ·
          refine ⟨4843486049693179732936121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3228990699795453155290747 4843486049693179732936121)
          ·
            refine ⟨3632614537269884799702091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4843486049693179732936121 3632614537269884799702091)
            ·
              refine ⟨5448921805904827199553137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3632614537269884799702091 5448921805904827199553137)
              ·
                refine ⟨4086691354428620399664853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5448921805904827199553137 4086691354428620399664853)
                ·
                  refine ⟨95781828619420790617145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4086691354428620399664853 95781828619420790617145)
                  ·
                    rfl

theorem cell22_839405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_839405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_839405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_839405 prefixEnd_839405 := by exact prefixLift 839405
  have htrace : WordTrace (prefixWord ++ tailWord_839405) baseStart_839405 baseEnd_839405 := by
    simpa [prefixWord, tailWord_839405, baseEnd_839405] using wordTrace_append hprefix tailTrace_839405
  have hstable : (prefixWord ++ tailWord_839405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839405).length < 2 ^ (prefixWord ++ tailWord_839405).sum := by decide
  have hdescent : baseEnd_839405 < baseStart_839405 := by decide
  rcases family_descends (prefixWord ++ tailWord_839405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839409 : List Nat := [1, 2, 2, 2, 2, 3, 3, 3, 1, 3]
def baseStart_839409 : Nat := 118140960795 + 839409 * 2 ^ 59
def prefixEnd_839409 : Nat := 4983230072969 + 3 ^ 40 * 839409 * 2
def baseEnd_839409 : Nat := 287346855140007694751423

theorem tailTrace_839409 : CollatzResearch.WordTrace tailWord_839409 prefixEnd_839409 287346855140007694751423 := by
  unfold tailWord_839409
  simp only [CollatzResearch.WordTrace]
  refine ⟨30615761415972027488865281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20410507610648018325910187 30615761415972027488865281)
  ·
    refine ⟨22961821061979020616648961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30615761415972027488865281 22961821061979020616648961)
    ·
      refine ⟨17221365796484265462486721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22961821061979020616648961 17221365796484265462486721)
      ·
        refine ⟨12916024347363199096865041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17221365796484265462486721 12916024347363199096865041)
        ·
          refine ⟨9687018260522399322648781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12916024347363199096865041 9687018260522399322648781)
          ·
            refine ⟨3632631847695899745993293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9687018260522399322648781 3632631847695899745993293)
            ·
              refine ⟨1362236942885962404747485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3632631847695899745993293 1362236942885962404747485)
              ·
                refine ⟨510838853582235901780307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1362236942885962404747485 510838853582235901780307)
                ·
                  refine ⟨766258280373353852670461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 510838853582235901780307 766258280373353852670461)
                  ·
                    refine ⟨287346855140007694751423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 766258280373353852670461 287346855140007694751423)
                    ·
                      rfl

theorem cell22_839409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 1, 3].length) (baseStart_839409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_839409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_839409 prefixEnd_839409 := by exact prefixLift 839409
  have htrace : WordTrace (prefixWord ++ tailWord_839409) baseStart_839409 baseEnd_839409 := by
    simpa [prefixWord, tailWord_839409, baseEnd_839409] using wordTrace_append hprefix tailTrace_839409
  have hstable : (prefixWord ++ tailWord_839409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839409).length < 2 ^ (prefixWord ++ tailWord_839409).sum := by decide
  have hdescent : baseEnd_839409 < baseStart_839409 := by decide
  rcases family_descends (prefixWord ++ tailWord_839409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839484 : List Nat := [2, 2, 2, 2, 1, 1, 6, 2, 4]
def baseStart_839484 : Nat := 118140960795 + 839484 * 2 ^ 59
def prefixEnd_839484 : Nat := 4983230072969 + 3 ^ 40 * 839484 * 2
def baseEnd_839484 : Nat := 95790843057577499708731

theorem tailTrace_839484 : CollatzResearch.WordTrace tailWord_839484 prefixEnd_839484 95790843057577499708731 := by
  unfold tailWord_839484
  simp only [CollatzResearch.WordTrace]
  refine ⟨15309248445350157648922753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20412331260466876865230337 15309248445350157648922753)
  ·
    refine ⟨11481936334012618236692065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15309248445350157648922753 11481936334012618236692065)
    ·
      refine ⟨8611452250509463677519049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11481936334012618236692065 8611452250509463677519049)
      ·
        refine ⟨6458589187882097758139287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8611452250509463677519049 6458589187882097758139287)
        ·
          refine ⟨9687883781823146637208931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6458589187882097758139287 9687883781823146637208931)
          ·
            refine ⟨14531825672734719955813397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9687883781823146637208931 14531825672734719955813397)
            ·
              refine ⟨681179328409439997928753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14531825672734719955813397 681179328409439997928753)
              ·
                refine ⟨510884496307079998446565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 681179328409439997928753 510884496307079998446565)
                ·
                  refine ⟨95790843057577499708731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 510884496307079998446565 95790843057577499708731)
                  ·
                    rfl

theorem cell22_839484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2, 4].length) (baseStart_839484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_839484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_839484 prefixEnd_839484 := by exact prefixLift 839484
  have htrace : WordTrace (prefixWord ++ tailWord_839484) baseStart_839484 baseEnd_839484 := by
    simpa [prefixWord, tailWord_839484, baseEnd_839484] using wordTrace_append hprefix tailTrace_839484
  have hstable : (prefixWord ++ tailWord_839484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839484).length < 2 ^ (prefixWord ++ tailWord_839484).sum := by decide
  have hdescent : baseEnd_839484 < baseStart_839484 := by decide
  rcases family_descends (prefixWord ++ tailWord_839484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839495 : List Nat := [1, 1, 4, 1, 2, 1, 5, 7]
def baseStart_839495 : Nat := 118140960795 + 839495 * 2 ^ 59
def prefixEnd_839495 : Nat := 4983230072969 + 3 ^ 40 * 839495 * 2
def baseEnd_839495 : Nat := 31930699410836904122351

theorem tailTrace_839495 : CollatzResearch.WordTrace tailWord_839495 prefixEnd_839495 31930699410836904122351 := by
  unfold tailWord_839495
  simp only [CollatzResearch.WordTrace]
  refine ⟨30618898093660464176495939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20412598729106976117663959 30618898093660464176495939)
  ·
    refine ⟨45928347140490696264743909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30618898093660464176495939 45928347140490696264743909)
    ·
      refine ⟨8611565088842005549639483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45928347140490696264743909 8611565088842005549639483)
      ·
        refine ⟨12917347633263008324459225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8611565088842005549639483 12917347633263008324459225)
        ·
          refine ⟨9688010724947256243344419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12917347633263008324459225 9688010724947256243344419)
          ·
            refine ⟨14532016087420884365016629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9688010724947256243344419 14532016087420884365016629)
            ·
              refine ⟨1362376508195707909220309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14532016087420884365016629 1362376508195707909220309)
              ·
                refine ⟨31930699410836904122351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1362376508195707909220309 31930699410836904122351)
                ·
                  rfl

theorem cell22_839495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 7].length) (baseStart_839495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_839495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_839495 prefixEnd_839495 := by exact prefixLift 839495
  have htrace : WordTrace (prefixWord ++ tailWord_839495) baseStart_839495 baseEnd_839495 := by
    simpa [prefixWord, tailWord_839495, baseEnd_839495] using wordTrace_append hprefix tailTrace_839495
  have hstable : (prefixWord ++ tailWord_839495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839495).length < 2 ^ (prefixWord ++ tailWord_839495).sum := by decide
  have hdescent : baseEnd_839495 < baseStart_839495 := by decide
  rcases family_descends (prefixWord ++ tailWord_839495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839527 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 5, 3]
def baseStart_839527 : Nat := 118140960795 + 839527 * 2 ^ 59
def prefixEnd_839527 : Nat := 4983230072969 + 3 ^ 40 * 839527 * 2
def baseEnd_839527 : Nat := 287387248951494720301061

theorem tailTrace_839527 : CollatzResearch.WordTrace tailWord_839527 prefixEnd_839527 287387248951494720301061 := by
  unfold tailWord_839527
  simp only [CollatzResearch.WordTrace]
  refine ⟨30620065229544533641660835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20413376819696355761107223 30620065229544533641660835)
  ·
    refine ⟨45930097844316800462491253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30620065229544533641660835 45930097844316800462491253)
    ·
      refine ⟨4305946672904700043358555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45930097844316800462491253 4305946672904700043358555)
      ·
        refine ⟨6458920009357050065037833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4305946672904700043358555 6458920009357050065037833)
        ·
          refine ⟨4844190007017787548778375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6458920009357050065037833 4844190007017787548778375)
          ·
            refine ⟨7266285010526681323167563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4844190007017787548778375 7266285010526681323167563)
            ·
              refine ⟨10899427515790021984751345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7266285010526681323167563 10899427515790021984751345)
              ·
                refine ⟨8174570636842516488563509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10899427515790021984751345 8174570636842516488563509)
                ·
                  refine ⟨766365997203985920802829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8174570636842516488563509 766365997203985920802829)
                  ·
                    refine ⟨287387248951494720301061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 766365997203985920802829 287387248951494720301061)
                    ·
                      rfl

theorem cell22_839527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_839527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_839527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_839527 prefixEnd_839527 := by exact prefixLift 839527
  have htrace : WordTrace (prefixWord ++ tailWord_839527) baseStart_839527 baseEnd_839527 := by
    simpa [prefixWord, tailWord_839527, baseEnd_839527] using wordTrace_append hprefix tailTrace_839527
  have hstable : (prefixWord ++ tailWord_839527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839527).length < 2 ^ (prefixWord ++ tailWord_839527).sum := by decide
  have hdescent : baseEnd_839527 < baseStart_839527 := by decide
  rcases family_descends (prefixWord ++ tailWord_839527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839578 : List Nat := [3, 1, 1, 4, 2, 3, 1, 3, 1, 3]
def baseStart_839578 : Nat := 118140960795 + 839578 * 2 ^ 59
def prefixEnd_839578 : Nat := 4983230072969 + 3 ^ 40 * 839578 * 2
def baseEnd_839578 : Nat := 287404707293747587275905

theorem tailTrace_839578 : CollatzResearch.WordTrace tailWord_839578 prefixEnd_839578 287404707293747587275905 := by
  unfold tailWord_839578
  simp only [CollatzResearch.WordTrace]
  refine ⟨7655481338089942337941847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20414616901573179567844925 7655481338089942337941847)
  ·
    refine ⟨11483222007134913506912771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7655481338089942337941847 11483222007134913506912771)
    ·
      refine ⟨17224833010702370260369157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11483222007134913506912771 17224833010702370260369157)
      ·
        refine ⟨3229656189506694423819217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17224833010702370260369157 3229656189506694423819217)
        ·
          refine ⟨2422242142130020817864413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3229656189506694423819217 2422242142130020817864413)
          ·
            refine ⟨908340803298757806699155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2422242142130020817864413 908340803298757806699155)
            ·
              refine ⟨1362511204948136710048733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 908340803298757806699155 1362511204948136710048733)
              ·
                refine ⟨510941701855551266268275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1362511204948136710048733 510941701855551266268275)
                ·
                  refine ⟨766412552783326899402413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 510941701855551266268275 766412552783326899402413)
                  ·
                    refine ⟨287404707293747587275905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 766412552783326899402413 287404707293747587275905)
                    ·
                      rfl

theorem cell22_839578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3, 1, 3].length) (baseStart_839578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_839578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_839578 prefixEnd_839578 := by exact prefixLift 839578
  have htrace : WordTrace (prefixWord ++ tailWord_839578) baseStart_839578 baseEnd_839578 := by
    simpa [prefixWord, tailWord_839578, baseEnd_839578] using wordTrace_append hprefix tailTrace_839578
  have hstable : (prefixWord ++ tailWord_839578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839578).length < 2 ^ (prefixWord ++ tailWord_839578).sum := by decide
  have hdescent : baseEnd_839578 < baseStart_839578 := by decide
  rcases family_descends (prefixWord ++ tailWord_839578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839632 : List Nat := [2, 1, 1, 1, 1, 2, 5, 3, 2, 4]
def baseStart_839632 : Nat := 118140960795 + 839632 * 2 ^ 59
def prefixEnd_839632 : Nat := 4983230072969 + 3 ^ 40 * 839632 * 2
def baseEnd_839632 : Nat := 287423192597309446425739

theorem tailTrace_839632 : CollatzResearch.WordTrace tailWord_839632 prefixEnd_839632 287423192597309446425739 := by
  unfold tailWord_839632
  simp only [CollatzResearch.WordTrace]
  refine ⟨15311947447082068287116575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20415929929442757716155433 15311947447082068287116575)
  ·
    refine ⟨22967921170623102430674863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15311947447082068287116575 22967921170623102430674863)
    ·
      refine ⟨34451881755934653646012295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22967921170623102430674863 34451881755934653646012295)
      ·
        refine ⟨51677822633901980469018443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34451881755934653646012295 51677822633901980469018443)
        ·
          refine ⟨77516733950852970703527665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51677822633901980469018443 77516733950852970703527665)
          ·
            refine ⟨58137550463139728027645749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77516733950852970703527665 58137550463139728027645749)
            ·
              refine ⟨5450395355919349502591789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58137550463139728027645749 5450395355919349502591789)
              ·
                refine ⟨2043898258469756063471921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5450395355919349502591789 2043898258469756063471921)
                ·
                  refine ⟨1532923693852317047603941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2043898258469756063471921 1532923693852317047603941)
                  ·
                    refine ⟨287423192597309446425739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1532923693852317047603941 287423192597309446425739)
                    ·
                      rfl

theorem cell22_839632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 2, 4].length) (baseStart_839632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_839632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_839632 prefixEnd_839632 := by exact prefixLift 839632
  have htrace : WordTrace (prefixWord ++ tailWord_839632) baseStart_839632 baseEnd_839632 := by
    simpa [prefixWord, tailWord_839632, baseEnd_839632] using wordTrace_append hprefix tailTrace_839632
  have hstable : (prefixWord ++ tailWord_839632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839632).length < 2 ^ (prefixWord ++ tailWord_839632).sum := by decide
  have hdescent : baseEnd_839632 < baseStart_839632 := by decide
  rcases family_descends (prefixWord ++ tailWord_839632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839651 : List Nat := [1, 1, 1, 6, 1, 3, 2, 2, 2, 3]
def baseStart_839651 : Nat := 118140960795 + 839651 * 2 ^ 59
def prefixEnd_839651 : Nat := 4983230072969 + 3 ^ 40 * 839651 * 2
def baseEnd_839651 : Nat := 287429696685599730200681

theorem tailTrace_839651 : CollatzResearch.WordTrace tailWord_839651 prefixEnd_839651 287429696685599730200681 := by
  unfold tailWord_839651
  simp only [CollatzResearch.WordTrace]
  refine ⟨30624587881095302819174807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20416391920730201879449871 30624587881095302819174807)
  ·
    refine ⟨45936881821642954228762211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30624587881095302819174807 45936881821642954228762211)
    ·
      refine ⟨68905322732464431343143317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45936881821642954228762211 68905322732464431343143317)
      ·
        refine ⟨3229937003084270219209843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68905322732464431343143317 3229937003084270219209843)
        ·
          refine ⟨4844905504626405328814765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3229937003084270219209843 4844905504626405328814765)
          ·
            refine ⟨1816839564234901998305537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4844905504626405328814765 1816839564234901998305537)
            ·
              refine ⟨1362629673176176498729153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1816839564234901998305537 1362629673176176498729153)
              ·
                refine ⟨1021972254882132374046865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1362629673176176498729153 1021972254882132374046865)
                ·
                  refine ⟨766479191161599280535149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1021972254882132374046865 766479191161599280535149)
                  ·
                    refine ⟨287429696685599730200681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 766479191161599280535149 287429696685599730200681)
                    ·
                      rfl

theorem cell22_839651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2, 3].length) (baseStart_839651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_839651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_839651 prefixEnd_839651 := by exact prefixLift 839651
  have htrace : WordTrace (prefixWord ++ tailWord_839651) baseStart_839651 baseEnd_839651 := by
    simpa [prefixWord, tailWord_839651, baseEnd_839651] using wordTrace_append hprefix tailTrace_839651
  have hstable : (prefixWord ++ tailWord_839651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839651).length < 2 ^ (prefixWord ++ tailWord_839651).sum := by decide
  have hdescent : baseEnd_839651 < baseStart_839651 := by decide
  rcases family_descends (prefixWord ++ tailWord_839651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839692 : List Nat := [2, 2, 1, 2, 3, 1, 2, 2, 7]
def baseStart_839692 : Nat := 118140960795 + 839692 * 2 ^ 59
def prefixEnd_839692 : Nat := 4983230072969 + 3 ^ 40 * 839692 * 2
def baseEnd_839692 : Nat := 95814577274496429975185

theorem tailTrace_839692 : CollatzResearch.WordTrace tailWord_839692 prefixEnd_839692 95814577274496429975185 := by
  unfold tailWord_839692
  simp only [CollatzResearch.WordTrace]
  refine ⟨15313041636973383410708665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20417388849297844547611553 15313041636973383410708665)
  ·
    refine ⟨11484781227730037558031499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15313041636973383410708665 11484781227730037558031499)
    ·
      refine ⟨17227171841595056337047249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11484781227730037558031499 17227171841595056337047249)
      ·
        refine ⟨12920378881196292252785437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17227171841595056337047249 12920378881196292252785437)
        ·
          refine ⟨4845142080448609594794539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12920378881196292252785437 4845142080448609594794539)
          ·
            refine ⟨7267713120672914392191809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4845142080448609594794539 7267713120672914392191809)
            ·
              refine ⟨5450784840504685794143857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7267713120672914392191809 5450784840504685794143857)
              ·
                refine ⟨4088088630378514345607893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5450784840504685794143857 4088088630378514345607893)
                ·
                  refine ⟨95814577274496429975185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4088088630378514345607893 95814577274496429975185)
                  ·
                    rfl

theorem cell22_839692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 7].length) (baseStart_839692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_839692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_839692 prefixEnd_839692 := by exact prefixLift 839692
  have htrace : WordTrace (prefixWord ++ tailWord_839692) baseStart_839692 baseEnd_839692 := by
    simpa [prefixWord, tailWord_839692, baseEnd_839692] using wordTrace_append hprefix tailTrace_839692
  have hstable : (prefixWord ++ tailWord_839692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839692).length < 2 ^ (prefixWord ++ tailWord_839692).sum := by decide
  have hdescent : baseEnd_839692 < baseStart_839692 := by decide
  rcases family_descends (prefixWord ++ tailWord_839692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839709 : List Nat := [1, 4, 2, 2, 2, 2, 1, 1, 7]
def baseStart_839709 : Nat := 118140960795 + 839709 * 2 ^ 59
def prefixEnd_839709 : Nat := 4983230072969 + 3 ^ 40 * 839709 * 2
def baseEnd_839709 : Nat := 95816517090302304083501

theorem tailTrace_839709 : CollatzResearch.WordTrace tailWord_839709 prefixEnd_839709 95816517090302304083501 := by
  unfold tailWord_839709
  simp only [CollatzResearch.WordTrace]
  refine ⟨30626703314885178724786181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20417802209923452483190787 30626703314885178724786181)
  ·
    refine ⟨5742506871540971010897409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30626703314885178724786181 5742506871540971010897409)
    ·
      refine ⟨4306880153655728258173057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5742506871540971010897409 4306880153655728258173057)
      ·
        refine ⟨3230160115241796193629793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4306880153655728258173057 3230160115241796193629793)
        ·
          refine ⟨2422620086431347145222345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3230160115241796193629793 2422620086431347145222345)
          ·
            refine ⟨1816965064823510358916759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2422620086431347145222345 1816965064823510358916759)
            ·
              refine ⟨2725447597235265538375139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1816965064823510358916759 2725447597235265538375139)
              ·
                refine ⟨4088171395852898307562709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2725447597235265538375139 4088171395852898307562709)
                ·
                  refine ⟨95816517090302304083501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4088171395852898307562709 95816517090302304083501)
                  ·
                    rfl

theorem cell22_839709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_839709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_839709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_839709 prefixEnd_839709 := by exact prefixLift 839709
  have htrace : WordTrace (prefixWord ++ tailWord_839709) baseStart_839709 baseEnd_839709 := by
    simpa [prefixWord, tailWord_839709, baseEnd_839709] using wordTrace_append hprefix tailTrace_839709
  have hstable : (prefixWord ++ tailWord_839709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839709).length < 2 ^ (prefixWord ++ tailWord_839709).sum := by decide
  have hdescent : baseEnd_839709 < baseStart_839709 := by decide
  rcases family_descends (prefixWord ++ tailWord_839709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839769 : List Nat := [1, 2, 1, 2, 2, 1, 3, 3, 4, 3]
def baseStart_839769 : Nat := 118140960795 + 839769 * 2 ^ 59
def prefixEnd_839769 : Nat := 4983230072969 + 3 ^ 40 * 839769 * 2
def baseEnd_839769 : Nat := 287470090497086755750319

theorem tailTrace_839769 : CollatzResearch.WordTrace tailWord_839769 prefixEnd_839769 287470090497086755750319 := by
  unfold tailWord_839769
  simp only [CollatzResearch.WordTrace]
  refine ⟨30628891694667808971970361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20419261129778539314646907 30628891694667808971970361)
  ·
    refine ⟨22971668771000856728977771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30628891694667808971970361 22971668771000856728977771)
    ·
      refine ⟨34457503156501285093466657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22971668771000856728977771 34457503156501285093466657)
      ·
        refine ⟨25843127367375963820099993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34457503156501285093466657 25843127367375963820099993)
        ·
          refine ⟨19382345525531972865074995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25843127367375963820099993 19382345525531972865074995)
          ·
            refine ⟨29073518288297959297612493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19382345525531972865074995 29073518288297959297612493)
            ·
              refine ⟨10902569358111734736604685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29073518288297959297612493 10902569358111734736604685)
              ·
                refine ⟨4088463509291900526226757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10902569358111734736604685 4088463509291900526226757)
                ·
                  refine ⟨766586907992231348667517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4088463509291900526226757 766586907992231348667517)
                  ·
                    refine ⟨287470090497086755750319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 766586907992231348667517 287470090497086755750319)
                    ·
                      rfl

theorem cell22_839769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4, 3].length) (baseStart_839769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_839769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_839769 prefixEnd_839769 := by exact prefixLift 839769
  have htrace : WordTrace (prefixWord ++ tailWord_839769) baseStart_839769 baseEnd_839769 := by
    simpa [prefixWord, tailWord_839769, baseEnd_839769] using wordTrace_append hprefix tailTrace_839769
  have hstable : (prefixWord ++ tailWord_839769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839769).length < 2 ^ (prefixWord ++ tailWord_839769).sum := by decide
  have hdescent : baseEnd_839769 < baseStart_839769 := by decide
  rcases family_descends (prefixWord ++ tailWord_839769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839801 : List Nat := [1, 2, 1, 3, 4, 2, 2, 1, 2, 4]
def baseStart_839801 : Nat := 118140960795 + 839801 * 2 ^ 59
def prefixEnd_839801 : Nat := 4983230072969 + 3 ^ 40 * 839801 * 2
def baseEnd_839801 : Nat := 287481044751049338950221

theorem tailTrace_839801 : CollatzResearch.WordTrace tailWord_839801 prefixEnd_839801 287481044751049338950221 := by
  unfold tailWord_839801
  simp only [CollatzResearch.WordTrace]
  refine ⟨30630058830551878437135257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20420039220367918958090171 30630058830551878437135257)
  ·
    refine ⟨22972544122913908827851443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30630058830551878437135257 22972544122913908827851443)
    ·
      refine ⟨34458816184370863241777165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22972544122913908827851443 34458816184370863241777165)
      ·
        refine ⟨12922056069139073715666437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34458816184370863241777165 12922056069139073715666437)
        ·
          refine ⟨2422885512963576321687457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12922056069139073715666437 2422885512963576321687457)
          ·
            refine ⟨1817164134722682241265593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2422885512963576321687457 1817164134722682241265593)
            ·
              refine ⟨1362873101042011680949195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1817164134722682241265593 1362873101042011680949195)
              ·
                refine ⟨2044309651563017521423793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1362873101042011680949195 2044309651563017521423793)
                ·
                  refine ⟨1533232238672263141067845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2044309651563017521423793 1533232238672263141067845)
                  ·
                    refine ⟨287481044751049338950221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1533232238672263141067845 287481044751049338950221)
                    ·
                      rfl

theorem cell22_839801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 4].length) (baseStart_839801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_839801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_839801 prefixEnd_839801 := by exact prefixLift 839801
  have htrace : WordTrace (prefixWord ++ tailWord_839801) baseStart_839801 baseEnd_839801 := by
    simpa [prefixWord, tailWord_839801, baseEnd_839801] using wordTrace_append hprefix tailTrace_839801
  have hstable : (prefixWord ++ tailWord_839801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839801).length < 2 ^ (prefixWord ++ tailWord_839801).sum := by decide
  have hdescent : baseEnd_839801 < baseStart_839801 := by decide
  rcases family_descends (prefixWord ++ tailWord_839801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839822 : List Nat := [4, 1, 1, 3, 4, 1, 2, 2, 4]
def baseStart_839822 : Nat := 118140960795 + 839822 * 2 ^ 59
def prefixEnd_839822 : Nat := 4983230072969 + 3 ^ 40 * 839822 * 2
def baseEnd_839822 : Nat := 95829411160070761391719

theorem tailTrace_839822 : CollatzResearch.WordTrace tailWord_839822 prefixEnd_839822 95829411160070761391719 := by
  unfold tailWord_839822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3828853095434474877956215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20420549842317199349099813 3828853095434474877956215)
  ·
    refine ⟨5743279643151712316934323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3828853095434474877956215 5743279643151712316934323)
    ·
      refine ⟨8614919464727568475401485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5743279643151712316934323 8614919464727568475401485)
      ·
        refine ⟨3230594799272838178275557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8614919464727568475401485 3230594799272838178275557)
        ·
          refine ⟨605736524863657158426667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3230594799272838178275557 605736524863657158426667)
          ·
            refine ⟨908604787295485737640001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605736524863657158426667 908604787295485737640001)
            ·
              refine ⟨681453590471614303230001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 908604787295485737640001 681453590471614303230001)
              ·
                refine ⟨511090192853710727422501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 681453590471614303230001 511090192853710727422501)
                ·
                  refine ⟨95829411160070761391719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 511090192853710727422501 95829411160070761391719)
                  ·
                    rfl

theorem cell22_839822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_839822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_839822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_839822 prefixEnd_839822 := by exact prefixLift 839822
  have htrace : WordTrace (prefixWord ++ tailWord_839822) baseStart_839822 baseEnd_839822 := by
    simpa [prefixWord, tailWord_839822, baseEnd_839822] using wordTrace_append hprefix tailTrace_839822
  have hstable : (prefixWord ++ tailWord_839822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839822).length < 2 ^ (prefixWord ++ tailWord_839822).sum := by decide
  have hdescent : baseEnd_839822 < baseStart_839822 := by decide
  rcases family_descends (prefixWord ++ tailWord_839822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839876 : List Nat := [2, 3, 3, 1, 2, 1, 1, 2, 2, 5]
def baseStart_839876 : Nat := 118140960795 + 839876 * 2 ^ 59
def prefixEnd_839876 : Nat := 4983230072969 + 3 ^ 40 * 839876 * 2
def baseEnd_839876 : Nat := 287506718783774143324991

theorem tailTrace_839876 : CollatzResearch.WordTrace tailWord_839876 prefixEnd_839876 287506718783774143324991 := by
  unfold tailWord_839876
  simp only [CollatzResearch.WordTrace]
  refine ⟨15316397152640083123057741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20421862870186777497410321 15316397152640083123057741)
  ·
    refine ⟨5743648932240031171146653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15316397152640083123057741 5743648932240031171146653)
    ·
      refine ⟨2153868349590011689179995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5743648932240031171146653 2153868349590011689179995)
      ·
        refine ⟨3230802524385017533769993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2153868349590011689179995 3230802524385017533769993)
        ·
          refine ⟨2423101893288763150327495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3230802524385017533769993 2423101893288763150327495)
          ·
            refine ⟨3634652839933144725491243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2423101893288763150327495 3634652839933144725491243)
            ·
              refine ⟨5451979259899717088236865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3634652839933144725491243 5451979259899717088236865)
              ·
                refine ⟨4088984444924787816177649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5451979259899717088236865 4088984444924787816177649)
                ·
                  refine ⟨3066738333693590862133237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4088984444924787816177649 3066738333693590862133237)
                  ·
                    refine ⟨287506718783774143324991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3066738333693590862133237 287506718783774143324991)
                    ·
                      rfl

theorem cell22_839876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_839876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_839876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_839876 prefixEnd_839876 := by exact prefixLift 839876
  have htrace : WordTrace (prefixWord ++ tailWord_839876) baseStart_839876 baseEnd_839876 := by
    simpa [prefixWord, tailWord_839876, baseEnd_839876] using wordTrace_append hprefix tailTrace_839876
  have hstable : (prefixWord ++ tailWord_839876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839876).length < 2 ^ (prefixWord ++ tailWord_839876).sum := by decide
  have hdescent : baseEnd_839876 < baseStart_839876 := by decide
  rcases family_descends (prefixWord ++ tailWord_839876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839889 : List Nat := [1, 2, 2, 1, 2, 2, 3, 3, 6]
def baseStart_839889 : Nat := 118140960795 + 839889 * 2 ^ 59
def prefixEnd_839889 : Nat := 4983230072969 + 3 ^ 40 * 839889 * 2
def baseEnd_839889 : Nat := 95837056316482147583317

theorem tailTrace_839889 : CollatzResearch.WordTrace tailWord_839889 prefixEnd_839889 95837056316482147583317 := by
  unfold tailWord_839889
  simp only [CollatzResearch.WordTrace]
  refine ⟨30633268454233069466338721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20422178969488712977559147 30633268454233069466338721)
  ·
    refine ⟨22974951340674802099754041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30633268454233069466338721 22974951340674802099754041)
    ·
      refine ⟨17231213505506101574815531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22974951340674802099754041 17231213505506101574815531)
      ·
        refine ⟨25846820258259152362223297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17231213505506101574815531 25846820258259152362223297)
        ·
          refine ⟨19385115193694364271667473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25846820258259152362223297 19385115193694364271667473)
          ·
            refine ⟨14538836395270773203750605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19385115193694364271667473 14538836395270773203750605)
            ·
              refine ⟨5452063648226539951406477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14538836395270773203750605 5452063648226539951406477)
              ·
                refine ⟨2044523868084952481777429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5452063648226539951406477 2044523868084952481777429)
                ·
                  refine ⟨95837056316482147583317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2044523868084952481777429 95837056316482147583317)
                  ·
                    rfl

theorem cell22_839889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 6].length) (baseStart_839889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_839889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_839889 prefixEnd_839889 := by exact prefixLift 839889
  have htrace : WordTrace (prefixWord ++ tailWord_839889) baseStart_839889 baseEnd_839889 := by
    simpa [prefixWord, tailWord_839889, baseEnd_839889] using wordTrace_append hprefix tailTrace_839889
  have hstable : (prefixWord ++ tailWord_839889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839889).length < 2 ^ (prefixWord ++ tailWord_839889).sum := by decide
  have hdescent : baseEnd_839889 < baseStart_839889 := by decide
  rcases family_descends (prefixWord ++ tailWord_839889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839921 : List Nat := [1, 2, 2, 2, 2, 1, 3, 2, 4, 3]
def baseStart_839921 : Nat := 118140960795 + 839921 * 2 ^ 59
def prefixEnd_839921 : Nat := 4983230072969 + 3 ^ 40 * 839921 * 2
def baseEnd_839921 : Nat := 287522123203409025949853

theorem tailTrace_839921 : CollatzResearch.WordTrace tailWord_839921 prefixEnd_839921 287522123203409025949853 := by
  unfold tailWord_839921
  simp only [CollatzResearch.WordTrace]
  refine ⟨30634435590117138931503617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20422957060078092621002411 30634435590117138931503617)
  ·
    refine ⟨22975826692587854198627713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30634435590117138931503617 22975826692587854198627713)
    ·
      refine ⟨17231870019440890648970785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22975826692587854198627713 17231870019440890648970785)
      ·
        refine ⟨12923902514580667986728089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17231870019440890648970785 12923902514580667986728089)
        ·
          refine ⟨9692926885935500990046067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12923902514580667986728089 9692926885935500990046067)
          ·
            refine ⟨14539390328903251485069101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9692926885935500990046067 14539390328903251485069101)
            ·
              refine ⟨5452271373338719306900913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14539390328903251485069101 5452271373338719306900913)
              ·
                refine ⟨4089203530004039480175685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5452271373338719306900913 4089203530004039480175685)
                ·
                  refine ⟨766725661875757402532941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4089203530004039480175685 766725661875757402532941)
                  ·
                    refine ⟨287522123203409025949853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 766725661875757402532941 287522123203409025949853)
                    ·
                      rfl

theorem cell22_839921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4, 3].length) (baseStart_839921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_839921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_839921 prefixEnd_839921 := by exact prefixLift 839921
  have htrace : WordTrace (prefixWord ++ tailWord_839921) baseStart_839921 baseEnd_839921 := by
    simpa [prefixWord, tailWord_839921, baseEnd_839921] using wordTrace_append hprefix tailTrace_839921
  have hstable : (prefixWord ++ tailWord_839921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839921).length < 2 ^ (prefixWord ++ tailWord_839921).sum := by decide
  have hdescent : baseEnd_839921 < baseStart_839921 := by decide
  rcases family_descends (prefixWord ++ tailWord_839921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839940 : List Nat := [2, 3, 2, 2, 4, 1, 1, 1, 6]
def baseStart_839940 : Nat := 118140960795 + 839940 * 2 ^ 59
def prefixEnd_839940 : Nat := 4983230072969 + 3 ^ 40 * 839940 * 2
def baseEnd_839940 : Nat := 95842875763899769908265

theorem tailTrace_839940 : CollatzResearch.WordTrace tailWord_839940 prefixEnd_839940 95842875763899769908265 := by
  unfold tailWord_839940
  simp only [CollatzResearch.WordTrace]
  refine ⟨15317564288524152588222637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20423419051365536784296849 15317564288524152588222637)
  ·
    refine ⟨5744086608196557220583489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15317564288524152588222637 5744086608196557220583489)
    ·
      refine ⟨4308064956147417915437617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5744086608196557220583489 4308064956147417915437617)
      ·
        refine ⟨3231048717110563436578213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4308064956147417915437617 3231048717110563436578213)
        ·
          refine ⟨605821634458230644358415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3231048717110563436578213 605821634458230644358415)
          ·
            refine ⟨908732451687345966537623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605821634458230644358415 908732451687345966537623)
            ·
              refine ⟨1363098677531018949806435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 908732451687345966537623 1363098677531018949806435)
              ·
                refine ⟨2044648016296528424709653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1363098677531018949806435 2044648016296528424709653)
                ·
                  refine ⟨95842875763899769908265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2044648016296528424709653 95842875763899769908265)
                  ·
                    rfl

theorem cell22_839940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_839940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_839940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_839940 prefixEnd_839940 := by exact prefixLift 839940
  have htrace : WordTrace (prefixWord ++ tailWord_839940) baseStart_839940 baseEnd_839940 := by
    simpa [prefixWord, tailWord_839940, baseEnd_839940] using wordTrace_append hprefix tailTrace_839940
  have hstable : (prefixWord ++ tailWord_839940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839940).length < 2 ^ (prefixWord ++ tailWord_839940).sum := by decide
  have hdescent : baseEnd_839940 < baseStart_839940 := by decide
  rcases family_descends (prefixWord ++ tailWord_839940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840071 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 3, 6]
def baseStart_840071 : Nat := 118140960795 + 840071 * 2 ^ 59
def prefixEnd_840071 : Nat := 4983230072969 + 3 ^ 40 * 840071 * 2
def baseEnd_840071 : Nat := 287573471268858634699393

theorem tailTrace_840071 : CollatzResearch.WordTrace tailWord_840071 prefixEnd_840071 287573471268858634699393 := by
  unfold tailWord_840071
  simp only [CollatzResearch.WordTrace]
  refine ⟨30639906539573714549464067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20426604359715809699642711 30639906539573714549464067)
  ·
    refine ⟨45959859809360571824196101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30639906539573714549464067 45959859809360571824196101)
    ·
      refine ⟨8617473714255107217036769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45959859809360571824196101 8617473714255107217036769)
      ·
        refine ⟨6463105285691330412777577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8617473714255107217036769 6463105285691330412777577)
        ·
          refine ⟨4847328964268497809583183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6463105285691330412777577 4847328964268497809583183)
          ·
            refine ⟨7270993446402746714374775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4847328964268497809583183 7270993446402746714374775)
            ·
              refine ⟨10906490169604120071562163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7270993446402746714374775 10906490169604120071562163)
              ·
                refine ⟨16359735254406180107343245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10906490169604120071562163 16359735254406180107343245)
                ·
                  refine ⟨6134900720402317540253717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16359735254406180107343245 6134900720402317540253717)
                  ·
                    refine ⟨287573471268858634699393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6134900720402317540253717 287573471268858634699393)
                    ·
                      rfl

theorem cell22_840071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_840071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840071 prefixEnd_840071 := by exact prefixLift 840071
  have htrace : WordTrace (prefixWord ++ tailWord_840071) baseStart_840071 baseEnd_840071 := by
    simpa [prefixWord, tailWord_840071, baseEnd_840071] using wordTrace_append hprefix tailTrace_840071
  have hstable : (prefixWord ++ tailWord_840071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840071).length < 2 ^ (prefixWord ++ tailWord_840071).sum := by decide
  have hdescent : baseEnd_840071 < baseStart_840071 := by decide
  rcases family_descends (prefixWord ++ tailWord_840071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840073 : List Nat := [1, 2, 1, 1, 6, 1, 3, 1, 1, 5]
def baseStart_840073 : Nat := 118140960795 + 840073 * 2 ^ 59
def prefixEnd_840073 : Nat := 4983230072969 + 3 ^ 40 * 840073 * 2
def baseEnd_840073 : Nat := 287574155909731296149387

theorem tailTrace_840073 : CollatzResearch.WordTrace tailWord_840073 prefixEnd_840073 287574155909731296149387 := by
  unfold tailWord_840073
  simp only [CollatzResearch.WordTrace]
  refine ⟨30639979485566468891036873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20426652990377645927357915 30639979485566468891036873)
  ·
    refine ⟨22979984614174851668277655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30639979485566468891036873 22979984614174851668277655)
    ·
      refine ⟨34469976921262277502416483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22979984614174851668277655 34469976921262277502416483)
      ·
        refine ⟨51704965381893416253624725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34469976921262277502416483 51704965381893416253624725)
        ·
          refine ⟨2423670252276253886888659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51704965381893416253624725 2423670252276253886888659)
          ·
            refine ⟨3635505378414380830332989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2423670252276253886888659 3635505378414380830332989)
            ·
              refine ⟨1363314516905392811374871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3635505378414380830332989 1363314516905392811374871)
              ·
                refine ⟨2044971775358089217062307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1363314516905392811374871 2044971775358089217062307)
                ·
                  refine ⟨3067457663037133825593461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2044971775358089217062307 3067457663037133825593461)
                  ·
                    refine ⟨287574155909731296149387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3067457663037133825593461 287574155909731296149387)
                    ·
                      rfl

theorem cell22_840073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 5].length) (baseStart_840073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840073 prefixEnd_840073 := by exact prefixLift 840073
  have htrace : WordTrace (prefixWord ++ tailWord_840073) baseStart_840073 baseEnd_840073 := by
    simpa [prefixWord, tailWord_840073, baseEnd_840073] using wordTrace_append hprefix tailTrace_840073
  have hstable : (prefixWord ++ tailWord_840073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840073).length < 2 ^ (prefixWord ++ tailWord_840073).sum := by decide
  have hdescent : baseEnd_840073 < baseStart_840073 := by decide
  rcases family_descends (prefixWord ++ tailWord_840073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840088 : List Nat := [2, 1, 2, 5, 1, 1, 2, 1, 1, 6]
def baseStart_840088 : Nat := 118140960795 + 840088 * 2 ^ 59
def prefixEnd_840088 : Nat := 4983230072969 + 3 ^ 40 * 840088 * 2
def baseEnd_840088 : Nat := 287579290716276257024341

theorem tailTrace_840088 : CollatzResearch.WordTrace tailWord_840088 prefixEnd_840088 287579290716276257024341 := by
  unfold tailWord_840088
  simp only [CollatzResearch.WordTrace]
  refine ⟨15320263290256063226416459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20427017720341417635221945 15320263290256063226416459)
  ·
    refine ⟨22980394935384094839624689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15320263290256063226416459 22980394935384094839624689)
    ·
      refine ⟨17235296201538071129718517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22980394935384094839624689 17235296201538071129718517)
      ·
        refine ⟨1615809018894194168411111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17235296201538071129718517 1615809018894194168411111)
        ·
          refine ⟨2423713528341291252616667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1615809018894194168411111 2423713528341291252616667)
          ·
            refine ⟨3635570292511936878925001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2423713528341291252616667 3635570292511936878925001)
            ·
              refine ⟨2726677719383952659193751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3635570292511936878925001 2726677719383952659193751)
              ·
                refine ⟨4090016579075928988790627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2726677719383952659193751 4090016579075928988790627)
                ·
                  refine ⟨6135024868613893483185941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4090016579075928988790627 6135024868613893483185941)
                  ·
                    refine ⟨287579290716276257024341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6135024868613893483185941 287579290716276257024341)
                    ·
                      rfl

theorem cell22_840088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_840088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840088 prefixEnd_840088 := by exact prefixLift 840088
  have htrace : WordTrace (prefixWord ++ tailWord_840088) baseStart_840088 baseEnd_840088 := by
    simpa [prefixWord, tailWord_840088, baseEnd_840088] using wordTrace_append hprefix tailTrace_840088
  have hstable : (prefixWord ++ tailWord_840088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840088).length < 2 ^ (prefixWord ++ tailWord_840088).sum := by decide
  have hdescent : baseEnd_840088 < baseStart_840088 := by decide
  rcases family_descends (prefixWord ++ tailWord_840088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840103 : List Nat := [1, 1, 6, 1, 1, 4, 8]
def baseStart_840103 : Nat := 118140960795 + 840103 * 2 ^ 59
def prefixEnd_840103 : Nat := 4983230072969 + 3 ^ 40 * 840103 * 2
def baseEnd_840103 : Nat := 10651275019363748811085

theorem tailTrace_840103 : CollatzResearch.WordTrace tailWord_840103 prefixEnd_840103 10651275019363748811085 := by
  unfold tailWord_840103
  simp only [CollatzResearch.WordTrace]
  refine ⟨30641073675457784014628963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20427382450305189343085975 30641073675457784014628963)
  ·
    refine ⟨45961610513186676021943445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30641073675457784014628963 45961610513186676021943445)
    ·
      refine ⟨2154450492805625438528599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45961610513186676021943445 2154450492805625438528599)
      ·
        refine ⟨3231675739208438157792899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2154450492805625438528599 3231675739208438157792899)
        ·
          refine ⟨4847513608812657236689349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3231675739208438157792899 4847513608812657236689349)
          ·
            refine ⟨908908801652373231879253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4847513608812657236689349 908908801652373231879253)
            ·
              refine ⟨10651275019363748811085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 908908801652373231879253 10651275019363748811085)
              ·
                rfl

theorem cell22_840103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 8].length) (baseStart_840103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840103 prefixEnd_840103 := by exact prefixLift 840103
  have htrace : WordTrace (prefixWord ++ tailWord_840103) baseStart_840103 baseEnd_840103 := by
    simpa [prefixWord, tailWord_840103, baseEnd_840103] using wordTrace_append hprefix tailTrace_840103
  have hstable : (prefixWord ++ tailWord_840103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840103).length < 2 ^ (prefixWord ++ tailWord_840103).sum := by decide
  have hdescent : baseEnd_840103 < baseStart_840103 := by decide
  rcases family_descends (prefixWord ++ tailWord_840103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840109 : List Nat := [1, 5, 2, 2, 2, 1, 3, 2, 4]
def baseStart_840109 : Nat := 118140960795 + 840109 * 2 ^ 59
def prefixEnd_840109 : Nat := 4983230072969 + 3 ^ 40 * 840109 * 2
def baseEnd_840109 : Nat := 95862159815146400749759

theorem tailTrace_840109 : CollatzResearch.WordTrace tailWord_840109 prefixEnd_840109 95862159815146400749759 := by
  unfold tailWord_840109
  simp only [CollatzResearch.WordTrace]
  refine ⟨30641292513436047039347381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20427528342290698026231587 30641292513436047039347381)
  ·
    refine ⟨2872621173134629409938817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30641292513436047039347381 2872621173134629409938817)
    ·
      refine ⟨2154465879850972057454113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2872621173134629409938817 2154465879850972057454113)
      ·
        refine ⟨1615849409888229043090585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2154465879850972057454113 1615849409888229043090585)
        ·
          refine ⟨1211887057416171782317939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1615849409888229043090585 1211887057416171782317939)
          ·
            refine ⟨1817830586124257673476909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211887057416171782317939 1817830586124257673476909)
            ·
              refine ⟨681686469796596627553841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1817830586124257673476909 681686469796596627553841)
              ·
                refine ⟨511264852347447470665381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 681686469796596627553841 511264852347447470665381)
                ·
                  refine ⟨95862159815146400749759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 511264852347447470665381 95862159815146400749759)
                  ·
                    rfl

theorem cell22_840109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_840109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840109 prefixEnd_840109 := by exact prefixLift 840109
  have htrace : WordTrace (prefixWord ++ tailWord_840109) baseStart_840109 baseEnd_840109 := by
    simpa [prefixWord, tailWord_840109, baseEnd_840109] using wordTrace_append hprefix tailTrace_840109
  have hstable : (prefixWord ++ tailWord_840109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840109).length < 2 ^ (prefixWord ++ tailWord_840109).sum := by decide
  have hdescent : baseEnd_840109 < baseStart_840109 := by decide
  rcases family_descends (prefixWord ++ tailWord_840109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840124 : List Nat := [2, 2, 2, 4, 1, 3, 2, 1, 2, 3]
def baseStart_840124 : Nat := 118140960795 + 840124 * 2 ^ 59
def prefixEnd_840124 : Nat := 4983230072969 + 3 ^ 40 * 840124 * 2
def baseEnd_840124 : Nat := 287591614251984163124231

theorem tailTrace_840124 : CollatzResearch.WordTrace tailWord_840124 prefixEnd_840124 287591614251984163124231 := by
  unfold tailWord_840124
  simp only [CollatzResearch.WordTrace]
  refine ⟨15320919804190852300571713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20427893072254469734095617 15320919804190852300571713)
  ·
    refine ⟨11490689853143139225428785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15320919804190852300571713 11490689853143139225428785)
    ·
      refine ⟨8618017389857354419071589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11490689853143139225428785 8618017389857354419071589)
      ·
        refine ⟨1615878260598253953575923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8618017389857354419071589 1615878260598253953575923)
        ·
          refine ⟨2423817390897380930363885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1615878260598253953575923 2423817390897380930363885)
          ·
            refine ⟨908931521586517848886457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2423817390897380930363885 908931521586517848886457)
            ·
              refine ⟨681698641189888386664843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 908931521586517848886457 681698641189888386664843)
              ·
                refine ⟨1022547961784832579997265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 681698641189888386664843 1022547961784832579997265)
                ·
                  refine ⟨766910971338624434997949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1022547961784832579997265 766910971338624434997949)
                  ·
                    refine ⟨287591614251984163124231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 766910971338624434997949 287591614251984163124231)
                    ·
                      rfl

theorem cell22_840124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_840124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840124 prefixEnd_840124 := by exact prefixLift 840124
  have htrace : WordTrace (prefixWord ++ tailWord_840124) baseStart_840124 baseEnd_840124 := by
    simpa [prefixWord, tailWord_840124, baseEnd_840124] using wordTrace_append hprefix tailTrace_840124
  have hstable : (prefixWord ++ tailWord_840124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840124).length < 2 ^ (prefixWord ++ tailWord_840124).sum := by decide
  have hdescent : baseEnd_840124 < baseStart_840124 := by decide
  rcases family_descends (prefixWord ++ tailWord_840124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840193 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 8]
def baseStart_840193 : Nat := 118140960795 + 840193 * 2 ^ 59
def prefixEnd_840193 : Nat := 4983230072969 + 3 ^ 40 * 840193 * 2
def baseEnd_840193 : Nat := 95871744787363661049673

theorem tailTrace_840193 : CollatzResearch.WordTrace tailWord_840193 prefixEnd_840193 95871744787363661049673 := by
  unfold tailWord_840193
  simp only [CollatzResearch.WordTrace]
  refine ⟨30644356245131729385405233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20429570830087819590270155 30644356245131729385405233)
  ·
    refine ⟨22983267183848797039053925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30644356245131729385405233 22983267183848797039053925)
    ·
      refine ⟨4309362596971649444822611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22983267183848797039053925 4309362596971649444822611)
      ·
        refine ⟨6464043895457474167233917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4309362596971649444822611 6464043895457474167233917)
        ·
          refine ⟨2424016460796552812712719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6464043895457474167233917 2424016460796552812712719)
          ·
            refine ⟨3636024691194829219069079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2424016460796552812712719 3636024691194829219069079)
            ·
              refine ⟨5454037036792243828603619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3636024691194829219069079 5454037036792243828603619)
              ·
                refine ⟨8181055555188365742905429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5454037036792243828603619 8181055555188365742905429)
                ·
                  refine ⟨95871744787363661049673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8181055555188365742905429 95871744787363661049673)
                  ·
                    rfl

theorem cell22_840193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 8].length) (baseStart_840193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840193 prefixEnd_840193 := by exact prefixLift 840193
  have htrace : WordTrace (prefixWord ++ tailWord_840193) baseStart_840193 baseEnd_840193 := by
    simpa [prefixWord, tailWord_840193, baseEnd_840193] using wordTrace_append hprefix tailTrace_840193
  have hstable : (prefixWord ++ tailWord_840193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840193).length < 2 ^ (prefixWord ++ tailWord_840193).sum := by decide
  have hdescent : baseEnd_840193 < baseStart_840193 := by decide
  rcases family_descends (prefixWord ++ tailWord_840193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840223 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 4, 4]
def baseStart_840223 : Nat := 118140960795 + 840223 * 2 ^ 59
def prefixEnd_840223 : Nat := 4983230072969 + 3 ^ 40 * 840223 * 2
def baseEnd_840223 : Nat := 287625503975180904898927

theorem tailTrace_840223 : CollatzResearch.WordTrace tailWord_840223 prefixEnd_840223 287625503975180904898927 := by
  unfold tailWord_840223
  simp only [CollatzResearch.WordTrace]
  refine ⟨30645450435023044508997323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20430300290015363005998215 30645450435023044508997323)
  ·
    refine ⟨45968175652534566763495985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30645450435023044508997323 45968175652534566763495985)
    ·
      refine ⟨34476131739400925072621989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45968175652534566763495985 34476131739400925072621989)
      ·
        refine ⟨6464274701137673451116623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34476131739400925072621989 6464274701137673451116623)
        ·
          refine ⟨9696412051706510176674935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6464274701137673451116623 9696412051706510176674935)
          ·
            refine ⟨14544618077559765265012403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9696412051706510176674935 14544618077559765265012403)
            ·
              refine ⟨21816927116339647897518605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14544618077559765265012403 21816927116339647897518605)
              ·
                refine ⟨8181347668627367961569477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21816927116339647897518605 8181347668627367961569477)
                ·
                  refine ⟨1534002687867631492794277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8181347668627367961569477 1534002687867631492794277)
                  ·
                    refine ⟨287625503975180904898927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1534002687867631492794277 287625503975180904898927)
                    ·
                      rfl

theorem cell22_840223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 4].length) (baseStart_840223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840223 prefixEnd_840223 := by exact prefixLift 840223
  have htrace : WordTrace (prefixWord ++ tailWord_840223) baseStart_840223 baseEnd_840223 := by
    simpa [prefixWord, tailWord_840223, baseEnd_840223] using wordTrace_append hprefix tailTrace_840223
  have hstable : (prefixWord ++ tailWord_840223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840223).length < 2 ^ (prefixWord ++ tailWord_840223).sum := by decide
  have hdescent : baseEnd_840223 < baseStart_840223 := by decide
  rcases family_descends (prefixWord ++ tailWord_840223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840225 : List Nat := [1, 2, 3, 2, 2, 1, 3, 1, 4, 3]
def baseStart_840225 : Nat := 118140960795 + 840225 * 2 ^ 59
def prefixEnd_840225 : Nat := 4983230072969 + 3 ^ 40 * 840225 * 2
def baseEnd_840225 : Nat := 287626188616053566348921

theorem tailTrace_840225 : CollatzResearch.WordTrace tailWord_840225 prefixEnd_840225 287626188616053566348921 := by
  unfold tailWord_840225
  simp only [CollatzResearch.WordTrace]
  refine ⟨30645523381015798850570129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20430348920677199233713419 30645523381015798850570129)
  ·
    refine ⟨22984142535761849137927597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30645523381015798850570129 22984142535761849137927597)
    ·
      refine ⟨8619053450910693426722849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22984142535761849137927597 8619053450910693426722849)
      ·
        refine ⟨6464290088183020070042137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8619053450910693426722849 6464290088183020070042137)
        ·
          refine ⟨4848217566137265052531603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6464290088183020070042137 4848217566137265052531603)
          ·
            refine ⟨7272326349205897578797405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4848217566137265052531603 7272326349205897578797405)
            ·
              refine ⟨2727122380952211592049027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7272326349205897578797405 2727122380952211592049027)
              ·
                refine ⟨4090683571428317388073541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2727122380952211592049027 4090683571428317388073541)
                ·
                  refine ⟨767003169642809510263789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4090683571428317388073541 767003169642809510263789)
                  ·
                    refine ⟨287626188616053566348921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 767003169642809510263789 287626188616053566348921)
                    ·
                      rfl

theorem cell22_840225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_840225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840225 prefixEnd_840225 := by exact prefixLift 840225
  have htrace : WordTrace (prefixWord ++ tailWord_840225) baseStart_840225 baseEnd_840225 := by
    simpa [prefixWord, tailWord_840225, baseEnd_840225] using wordTrace_append hprefix tailTrace_840225
  have hstable : (prefixWord ++ tailWord_840225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840225).length < 2 ^ (prefixWord ++ tailWord_840225).sum := by decide
  have hdescent : baseEnd_840225 < baseStart_840225 := by decide
  rcases family_descends (prefixWord ++ tailWord_840225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840270 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 5, 3]
def baseStart_840270 : Nat := 118140960795 + 840270 * 2 ^ 59
def prefixEnd_840270 : Nat := 4983230072969 + 3 ^ 40 * 840270 * 2
def baseEnd_840270 : Nat := 287641593035688448973783

theorem tailTrace_840270 : CollatzResearch.WordTrace tailWord_840270 prefixEnd_840270 287641593035688448973783 := by
  unfold tailWord_840270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3830895583231596441994783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20431443110568514357305509 3830895583231596441994783)
  ·
    refine ⟨5746343374847394662992175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3830895583231596441994783 5746343374847394662992175)
    ·
      refine ⟨8619515062271091994488263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5746343374847394662992175 8619515062271091994488263)
      ·
        refine ⟨12929272593406637991732395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8619515062271091994488263 12929272593406637991732395)
        ·
          refine ⟨19393908890109956987598593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12929272593406637991732395 19393908890109956987598593)
          ·
            refine ⟨14545431667582467740698945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19393908890109956987598593 14545431667582467740698945)
            ·
              refine ⟨10909073750686850805524209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14545431667582467740698945 10909073750686850805524209)
              ·
                refine ⟨8181805313015138104143157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10909073750686850805524209 8181805313015138104143157)
                ·
                  refine ⟨767044248095169197263421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8181805313015138104143157 767044248095169197263421)
                  ·
                    refine ⟨287641593035688448973783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 767044248095169197263421 287641593035688448973783)
                    ·
                      rfl

theorem cell22_840270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_840270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840270 prefixEnd_840270 := by exact prefixLift 840270
  have htrace : WordTrace (prefixWord ++ tailWord_840270) baseStart_840270 baseEnd_840270 := by
    simpa [prefixWord, tailWord_840270, baseEnd_840270] using wordTrace_append hprefix tailTrace_840270
  have hstable : (prefixWord ++ tailWord_840270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840270).length < 2 ^ (prefixWord ++ tailWord_840270).sum := by decide
  have hdescent : baseEnd_840270 < baseStart_840270 := by decide
  rcases family_descends (prefixWord ++ tailWord_840270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840287 : List Nat := [1, 1, 2, 3, 1, 1, 1, 8, 1, 3]
def baseStart_840287 : Nat := 118140960795 + 840287 * 2 ^ 59
def prefixEnd_840287 : Nat := 4983230072969 + 3 ^ 40 * 840287 * 2
def baseEnd_840287 : Nat := 287647412483106071298731

theorem tailTrace_840287 : CollatzResearch.WordTrace tailWord_840287 prefixEnd_840287 287647412483106071298731 := by
  unfold tailWord_840287
  simp only [CollatzResearch.WordTrace]
  refine ⟨30647784706791183439327115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20431856471194122292884743 30647784706791183439327115)
  ·
    refine ⟨45971677060186775158990673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30647784706791183439327115 45971677060186775158990673)
    ·
      refine ⟨34478757795140081369243005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45971677060186775158990673 34478757795140081369243005)
      ·
        refine ⟨12929534173177530513466127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34478757795140081369243005 12929534173177530513466127)
        ·
          refine ⟨19394301259766295770199191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12929534173177530513466127 19394301259766295770199191)
          ·
            refine ⟨29091451889649443655298787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19394301259766295770199191 29091451889649443655298787)
            ·
              refine ⟨43637177834474165482948181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29091451889649443655298787 43637177834474165482948181)
              ·
                refine ⟨511373177747744126753299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 43637177834474165482948181 511373177747744126753299)
                ·
                  refine ⟨767059766621616190129949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 511373177747744126753299 767059766621616190129949)
                  ·
                    refine ⟨287647412483106071298731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 767059766621616190129949 287647412483106071298731)
                    ·
                      rfl

theorem cell22_840287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8, 1, 3].length) (baseStart_840287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840287 prefixEnd_840287 := by exact prefixLift 840287
  have htrace : WordTrace (prefixWord ++ tailWord_840287) baseStart_840287 baseEnd_840287 := by
    simpa [prefixWord, tailWord_840287, baseEnd_840287] using wordTrace_append hprefix tailTrace_840287
  have hstable : (prefixWord ++ tailWord_840287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840287).length < 2 ^ (prefixWord ++ tailWord_840287).sum := by decide
  have hdescent : baseEnd_840287 < baseStart_840287 := by decide
  rcases family_descends (prefixWord ++ tailWord_840287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840338 : List Nat := [3, 2, 3, 1, 2, 3, 2, 2, 1, 3]
def baseStart_840338 : Nat := 118140960795 + 840338 * 2 ^ 59
def prefixEnd_840338 : Nat := 4983230072969 + 3 ^ 40 * 840338 * 2
def baseEnd_840338 : Nat := 287664870825358938273575

theorem tailTrace_840338 : CollatzResearch.WordTrace tailWord_840338 prefixEnd_840338 287664870825358938273575 := by
  unfold tailWord_840338
  simp only [CollatzResearch.WordTrace]
  refine ⟨7662411207401604787358417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20433096553070946099622445 7662411207401604787358417)
  ·
    refine ⟨5746808405551203590518813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7662411207401604787358417 5746808405551203590518813)
    ·
      refine ⟨2155053152081701346444555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5746808405551203590518813 2155053152081701346444555)
      ·
        refine ⟨3232579728122552019666833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2155053152081701346444555 3232579728122552019666833)
        ·
          refine ⟨2424434796091914014750125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3232579728122552019666833 2424434796091914014750125)
          ·
            refine ⟨909163048534467755531297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2424434796091914014750125 909163048534467755531297)
            ·
              refine ⟨681872286400850816648473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 909163048534467755531297 681872286400850816648473)
              ·
                refine ⟨511404214800638112486355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 681872286400850816648473 511404214800638112486355)
                ·
                  refine ⟨767106322200957168729533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 511404214800638112486355 767106322200957168729533)
                  ·
                    refine ⟨287664870825358938273575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 767106322200957168729533 287664870825358938273575)
                    ·
                      rfl

theorem cell22_840338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_840338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840338 prefixEnd_840338 := by exact prefixLift 840338
  have htrace : WordTrace (prefixWord ++ tailWord_840338) baseStart_840338 baseEnd_840338 := by
    simpa [prefixWord, tailWord_840338, baseEnd_840338] using wordTrace_append hprefix tailTrace_840338
  have hstable : (prefixWord ++ tailWord_840338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840338).length < 2 ^ (prefixWord ++ tailWord_840338).sum := by decide
  have hdescent : baseEnd_840338 < baseStart_840338 := by decide
  rcases family_descends (prefixWord ++ tailWord_840338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840394 : List Nat := [3, 1, 2, 1, 4, 1, 3, 2, 2, 3]
def baseStart_840394 : Nat := 118140960795 + 840394 * 2 ^ 59
def prefixEnd_840394 : Nat := 4983230072969 + 3 ^ 40 * 840394 * 2
def baseEnd_840394 : Nat := 287684040769793458873403

theorem tailTrace_840394 : CollatzResearch.WordTrace tailWord_840394 prefixEnd_840394 287684040769793458873403 := by
  unfold tailWord_840394
  simp only [CollatzResearch.WordTrace]
  refine ⟨7662921829350885178368059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20434458211602360475648157 7662921829350885178368059)
  ·
    refine ⟨11494382744026327767552089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7662921829350885178368059 11494382744026327767552089)
    ·
      refine ⟨8620787058019745825664067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11494382744026327767552089 8620787058019745825664067)
      ·
        refine ⟨12931180587029618738496101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8620787058019745825664067 12931180587029618738496101)
        ·
          refine ⟨2424596360068053513468019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12931180587029618738496101 2424596360068053513468019)
          ·
            refine ⟨3636894540102080270202029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2424596360068053513468019 3636894540102080270202029)
            ·
              refine ⟨1363835452538280101325761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3636894540102080270202029 1363835452538280101325761)
              ·
                refine ⟨1022876589403710075994321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1363835452538280101325761 1022876589403710075994321)
                ·
                  refine ⟨767157442052782556995741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1022876589403710075994321 767157442052782556995741)
                  ·
                    refine ⟨287684040769793458873403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 767157442052782556995741 287684040769793458873403)
                    ·
                      rfl

theorem cell22_840394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_840394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840394 prefixEnd_840394 := by exact prefixLift 840394
  have htrace : WordTrace (prefixWord ++ tailWord_840394) baseStart_840394 baseEnd_840394 := by
    simpa [prefixWord, tailWord_840394, baseEnd_840394] using wordTrace_append hprefix tailTrace_840394
  have hstable : (prefixWord ++ tailWord_840394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840394).length < 2 ^ (prefixWord ++ tailWord_840394).sum := by decide
  have hdescent : baseEnd_840394 < baseStart_840394 := by decide
  rcases family_descends (prefixWord ++ tailWord_840394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840424 : List Nat := [2, 1, 4, 1, 4, 2, 2, 6]
def baseStart_840424 : Nat := 118140960795 + 840424 * 2 ^ 59
def prefixEnd_840424 : Nat := 4983230072969 + 3 ^ 40 * 840424 * 2
def baseEnd_840424 : Nat := 31966034486987042291479

theorem tailTrace_840424 : CollatzResearch.WordTrace tailWord_840424 prefixEnd_840424 31966034486987042291479 := by
  unfold tailWord_840424
  simp only [CollatzResearch.WordTrace]
  refine ⟨15326390753647427918532163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20435187671529903891376217 15326390753647427918532163)
  ·
    refine ⟨22989586130471141877798245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15326390753647427918532163 22989586130471141877798245)
    ·
      refine ⟨4310547399463339102087171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22989586130471141877798245 4310547399463339102087171)
      ·
        refine ⟨6465821099195008653130757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4310547399463339102087171 6465821099195008653130757)
        ·
          refine ⟨1212341456099064122462017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6465821099195008653130757 1212341456099064122462017)
          ·
            refine ⟨909256092074298091846513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1212341456099064122462017 909256092074298091846513)
            ·
              refine ⟨681942069055723568884885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 909256092074298091846513 681942069055723568884885)
              ·
                refine ⟨31966034486987042291479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 681942069055723568884885 31966034486987042291479)
                ·
                  rfl

theorem cell22_840424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 6].length) (baseStart_840424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840424 prefixEnd_840424 := by exact prefixLift 840424
  have htrace : WordTrace (prefixWord ++ tailWord_840424) baseStart_840424 baseEnd_840424 := by
    simpa [prefixWord, tailWord_840424, baseEnd_840424] using wordTrace_append hprefix tailTrace_840424
  have hstable : (prefixWord ++ tailWord_840424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840424).length < 2 ^ (prefixWord ++ tailWord_840424).sum := by decide
  have hdescent : baseEnd_840424 < baseStart_840424 := by decide
  rcases family_descends (prefixWord ++ tailWord_840424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840452 : List Nat := [2, 3, 2, 2, 1, 1, 2, 4, 5]
def baseStart_840452 : Nat := 118140960795 + 840452 * 2 ^ 59
def prefixEnd_840452 : Nat := 4983230072969 + 3 ^ 40 * 840452 * 2
def baseEnd_840452 : Nat := 95901298451700213641075

theorem tailTrace_840452 : CollatzResearch.WordTrace tailWord_840452 prefixEnd_840452 95901298451700213641075 := by
  unfold tailWord_840452
  simp only [CollatzResearch.WordTrace]
  refine ⟨15326901375596708309541805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20435868500795611079389073 15326901375596708309541805)
  ·
    refine ⟨5747588015848765616078177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15326901375596708309541805 5747588015848765616078177)
    ·
      refine ⟨4310691011886574212058633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5747588015848765616078177 4310691011886574212058633)
      ·
        refine ⟨3233018258914930659043975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4310691011886574212058633 3233018258914930659043975)
        ·
          refine ⟨4849527388372395988565963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3233018258914930659043975 4849527388372395988565963)
          ·
            refine ⟨7274291082558593982848945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4849527388372395988565963 7274291082558593982848945)
            ·
              refine ⟨5455718311918945487136709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7274291082558593982848945 5455718311918945487136709)
              ·
                refine ⟨1022947183484802278838133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5455718311918945487136709 1022947183484802278838133)
                ·
                  refine ⟨95901298451700213641075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1022947183484802278838133 95901298451700213641075)
                  ·
                    rfl

theorem cell22_840452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_840452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840452 prefixEnd_840452 := by exact prefixLift 840452
  have htrace : WordTrace (prefixWord ++ tailWord_840452) baseStart_840452 baseEnd_840452 := by
    simpa [prefixWord, tailWord_840452, baseEnd_840452] using wordTrace_append hprefix tailTrace_840452
  have hstable : (prefixWord ++ tailWord_840452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840452).length < 2 ^ (prefixWord ++ tailWord_840452).sum := by decide
  have hdescent : baseEnd_840452 < baseStart_840452 := by decide
  rcases family_descends (prefixWord ++ tailWord_840452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840512 : List Nat := [2, 1, 1, 2, 2, 1, 1, 5, 4, 3]
def baseStart_840512 : Nat := 118140960795 + 840512 * 2 ^ 59
def prefixEnd_840512 : Nat := 4983230072969 + 3 ^ 40 * 840512 * 2
def baseEnd_840512 : Nat := 287724434581280484423041

theorem tailTrace_840512 : CollatzResearch.WordTrace tailWord_840512 prefixEnd_840512 287724434581280484423041 := by
  unfold tailWord_840512
  simp only [CollatzResearch.WordTrace]
  refine ⟨15327995565488023433133895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20437327420650697910845193 15327995565488023433133895)
  ·
    refine ⟨22991993348232035149700843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15327995565488023433133895 22991993348232035149700843)
    ·
      refine ⟨34487990022348052724551265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22991993348232035149700843 34487990022348052724551265)
      ·
        refine ⟨25865992516761039543413449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34487990022348052724551265 25865992516761039543413449)
        ·
          refine ⟨19399494387570779657560087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25865992516761039543413449 19399494387570779657560087)
          ·
            refine ⟨29099241581356169486340131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19399494387570779657560087 29099241581356169486340131)
            ·
              refine ⟨43648862372034254229510197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29099241581356169486340131 43648862372034254229510197)
              ·
                refine ⟨4092080847378211334016581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43648862372034254229510197 4092080847378211334016581)
                ·
                  refine ⟨767265158883414625128109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4092080847378211334016581 767265158883414625128109)
                  ·
                    refine ⟨287724434581280484423041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 767265158883414625128109 287724434581280484423041)
                    ·
                      rfl

theorem cell22_840512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 4, 3].length) (baseStart_840512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840512 prefixEnd_840512 := by exact prefixLift 840512
  have htrace : WordTrace (prefixWord ++ tailWord_840512) baseStart_840512 baseEnd_840512 := by
    simpa [prefixWord, tailWord_840512, baseEnd_840512] using wordTrace_append hprefix tailTrace_840512
  have hstable : (prefixWord ++ tailWord_840512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840512).length < 2 ^ (prefixWord ++ tailWord_840512).sum := by decide
  have hdescent : baseEnd_840512 < baseStart_840512 := by decide
  rcases family_descends (prefixWord ++ tailWord_840512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840529 : List Nat := [1, 2, 2, 1, 6, 1, 2, 1, 1, 5]
def baseStart_840529 : Nat := 118140960795 + 840529 * 2 ^ 59
def prefixEnd_840529 : Nat := 4983230072969 + 3 ^ 40 * 840529 * 2
def baseEnd_840529 : Nat := 287730254028698106747989

theorem tailTrace_840529 : CollatzResearch.WordTrace tailWord_840529 prefixEnd_840529 287730254028698106747989 := by
  unfold tailWord_840529
  simp only [CollatzResearch.WordTrace]
  refine ⟨30656611171914458769636641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20437740781276305846424427 30656611171914458769636641)
  ·
    refine ⟨22992458378935844077227481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30656611171914458769636641 22992458378935844077227481)
    ·
      refine ⟨17244343784201883057920611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22992458378935844077227481 17244343784201883057920611)
      ·
        refine ⟨25866515676302824586880917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17244343784201883057920611 25866515676302824586880917)
        ·
          refine ⟨1212492922326694902510043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25866515676302824586880917 1212492922326694902510043)
          ·
            refine ⟨1818739383490042353765065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1212492922326694902510043 1818739383490042353765065)
            ·
              refine ⟨1364054537617531765323799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1818739383490042353765065 1364054537617531765323799)
              ·
                refine ⟨2046081806426297647985699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1364054537617531765323799 2046081806426297647985699)
                ·
                  refine ⟨3069122709639446471978549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2046081806426297647985699 3069122709639446471978549)
                  ·
                    refine ⟨287730254028698106747989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3069122709639446471978549 287730254028698106747989)
                    ·
                      rfl

theorem cell22_840529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_840529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840529 prefixEnd_840529 := by exact prefixLift 840529
  have htrace : WordTrace (prefixWord ++ tailWord_840529) baseStart_840529 baseEnd_840529 := by
    simpa [prefixWord, tailWord_840529, baseEnd_840529] using wordTrace_append hprefix tailTrace_840529
  have hstable : (prefixWord ++ tailWord_840529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840529).length < 2 ^ (prefixWord ++ tailWord_840529).sum := by decide
  have hdescent : baseEnd_840529 < baseStart_840529 := by decide
  rcases family_descends (prefixWord ++ tailWord_840529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840587 : List Nat := [1, 1, 1, 1, 4, 2, 2, 5, 5]
def baseStart_840587 : Nat := 118140960795 + 840587 * 2 ^ 59
def prefixEnd_840587 : Nat := 4983230072969 + 3 ^ 40 * 840587 * 2
def baseEnd_840587 : Nat := 95916702871335096265937

theorem tailTrace_840587 : CollatzResearch.WordTrace tailWord_840587 prefixEnd_840587 95916702871335096265937 := by
  unfold tailWord_840587
  simp only [CollatzResearch.WordTrace]
  refine ⟨30658726605704334675248015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20439151070469556450165343 30658726605704334675248015)
  ·
    refine ⟨45988089908556502012872023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30658726605704334675248015 45988089908556502012872023)
    ·
      refine ⟨68982134862834753019308035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45988089908556502012872023 68982134862834753019308035)
      ·
        refine ⟨103473202294252129528962053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68982134862834753019308035 103473202294252129528962053)
        ·
          refine ⟨19401225430172274286680385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103473202294252129528962053 19401225430172274286680385)
          ·
            refine ⟨14550919072629205715010289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19401225430172274286680385 14550919072629205715010289)
            ·
              refine ⟨10913189304471904286257717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14550919072629205715010289 10913189304471904286257717)
              ·
                refine ⟨1023111497294241026836661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10913189304471904286257717 1023111497294241026836661)
                ·
                  refine ⟨95916702871335096265937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1023111497294241026836661 95916702871335096265937)
                  ·
                    rfl

theorem cell22_840587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 5].length) (baseStart_840587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840587 prefixEnd_840587 := by exact prefixLift 840587
  have htrace : WordTrace (prefixWord ++ tailWord_840587) baseStart_840587 baseEnd_840587 := by
    simpa [prefixWord, tailWord_840587, baseEnd_840587] using wordTrace_append hprefix tailTrace_840587
  have hstable : (prefixWord ++ tailWord_840587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840587).length < 2 ^ (prefixWord ++ tailWord_840587).sum := by decide
  have hdescent : baseEnd_840587 < baseStart_840587 := by decide
  rcases family_descends (prefixWord ++ tailWord_840587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840625 : List Nat := [1, 2, 2, 4, 3, 1, 3, 2, 1, 3]
def baseStart_840625 : Nat := 118140960795 + 840625 * 2 ^ 59
def prefixEnd_840625 : Nat := 4983230072969 + 3 ^ 40 * 840625 * 2
def baseEnd_840625 : Nat := 287763116790585856347695

theorem tailTrace_840625 : CollatzResearch.WordTrace tailWord_840625 prefixEnd_840625 287763116790585856347695 := by
  unfold tailWord_840625
  simp only [CollatzResearch.WordTrace]
  refine ⟨30660112579566667165131329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20440075053044444776754219 30660112579566667165131329)
  ·
    refine ⟨22995084434675000373848497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30660112579566667165131329 22995084434675000373848497)
    ·
      refine ⟨17246313326006250280386373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22995084434675000373848497 17246313326006250280386373)
      ·
        refine ⟨3233683748626171927572445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17246313326006250280386373 3233683748626171927572445)
        ·
          refine ⟨1212631405734814472839667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3233683748626171927572445 1212631405734814472839667)
          ·
            refine ⟨1818947108602221709259501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1212631405734814472839667 1818947108602221709259501)
            ·
              refine ⟨682105165725833140972313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1818947108602221709259501 682105165725833140972313)
              ·
                refine ⟨511578874294374855729235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 682105165725833140972313 511578874294374855729235)
                ·
                  refine ⟨767368311441562283593853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 511578874294374855729235 767368311441562283593853)
                  ·
                    refine ⟨287763116790585856347695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 767368311441562283593853 287763116790585856347695)
                    ·
                      rfl

theorem cell22_840625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2, 1, 3].length) (baseStart_840625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840625 prefixEnd_840625 := by exact prefixLift 840625
  have htrace : WordTrace (prefixWord ++ tailWord_840625) baseStart_840625 baseEnd_840625 := by
    simpa [prefixWord, tailWord_840625, baseEnd_840625] using wordTrace_append hprefix tailTrace_840625
  have hstable : (prefixWord ++ tailWord_840625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840625).length < 2 ^ (prefixWord ++ tailWord_840625).sum := by decide
  have hdescent : baseEnd_840625 < baseStart_840625 := by decide
  rcases family_descends (prefixWord ++ tailWord_840625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840651 : List Nat := [1, 1, 1, 1, 3, 7, 1, 2, 1, 4]
def baseStart_840651 : Nat := 118140960795 + 840651 * 2 ^ 59
def prefixEnd_840651 : Nat := 4983230072969 + 3 ^ 40 * 840651 * 2
def baseEnd_840651 : Nat := 287772017121930455197615

theorem tailTrace_840651 : CollatzResearch.WordTrace tailWord_840651 prefixEnd_840651 287772017121930455197615 := by
  unfold tailWord_840651
  simp only [CollatzResearch.WordTrace]
  refine ⟨30661060877472473605577807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20440707251648315737051871 30661060877472473605577807)
  ·
    refine ⟨45991591316208710408366711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30661060877472473605577807 45991591316208710408366711)
    ·
      refine ⟨68987386974313065612550067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45991591316208710408366711 68987386974313065612550067)
      ·
        refine ⟨103481080461469598418825101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68987386974313065612550067 103481080461469598418825101)
        ·
          refine ⟨38805405173051099407059413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103481080461469598418825101 38805405173051099407059413)
          ·
            refine ⟨909501683743385142352955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 38805405173051099407059413 909501683743385142352955)
            ·
              refine ⟨1364252525615077713529433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909501683743385142352955 1364252525615077713529433)
              ·
                refine ⟨1023189394211308285147075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1364252525615077713529433 1023189394211308285147075)
                ·
                  refine ⟨1534784091316962427720613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1023189394211308285147075 1534784091316962427720613)
                  ·
                    refine ⟨287772017121930455197615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1534784091316962427720613 287772017121930455197615)
                    ·
                      rfl

theorem cell22_840651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 4].length) (baseStart_840651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840651 prefixEnd_840651 := by exact prefixLift 840651
  have htrace : WordTrace (prefixWord ++ tailWord_840651) baseStart_840651 baseEnd_840651 := by
    simpa [prefixWord, tailWord_840651, baseEnd_840651] using wordTrace_append hprefix tailTrace_840651
  have hstable : (prefixWord ++ tailWord_840651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840651).length < 2 ^ (prefixWord ++ tailWord_840651).sum := by decide
  have hdescent : baseEnd_840651 < baseStart_840651 := by decide
  rcases family_descends (prefixWord ++ tailWord_840651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840664 : List Nat := [2, 1, 2, 2, 2, 4, 1, 2, 1, 5]
def baseStart_840664 : Nat := 118140960795 + 840664 * 2 ^ 59
def prefixEnd_840664 : Nat := 4983230072969 + 3 ^ 40 * 840664 * 2
def baseEnd_840664 : Nat := 287776467287602754622575

theorem tailTrace_840664 : CollatzResearch.WordTrace tailWord_840664 prefixEnd_840664 287776467287602754622575 := by
  unfold tailWord_840664
  simp only [CollatzResearch.WordTrace]
  refine ⟨15330767513212688412900523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20441023350950251217200697 15330767513212688412900523)
  ·
    refine ⟨22996151269819032619350785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15330767513212688412900523 22996151269819032619350785)
    ·
      refine ⟨17247113452364274464513089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22996151269819032619350785 17247113452364274464513089)
      ·
        refine ⟨12935335089273205848384817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17247113452364274464513089 12935335089273205848384817)
        ·
          refine ⟨9701501316954904386288613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12935335089273205848384817 9701501316954904386288613)
          ·
            refine ⟨1819031496929044572429115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9701501316954904386288613 1819031496929044572429115)
            ·
              refine ⟨2728547245393566858643673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1819031496929044572429115 2728547245393566858643673)
              ·
                refine ⟨2046410434045175143982755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2728547245393566858643673 2046410434045175143982755)
                ·
                  refine ⟨3069615651067762715974133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2046410434045175143982755 3069615651067762715974133)
                  ·
                    refine ⟨287776467287602754622575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3069615651067762715974133 287776467287602754622575)
                    ·
                      rfl

theorem cell22_840664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_840664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840664 prefixEnd_840664 := by exact prefixLift 840664
  have htrace : WordTrace (prefixWord ++ tailWord_840664) baseStart_840664 baseEnd_840664 := by
    simpa [prefixWord, tailWord_840664, baseEnd_840664] using wordTrace_append hprefix tailTrace_840664
  have hstable : (prefixWord ++ tailWord_840664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840664).length < 2 ^ (prefixWord ++ tailWord_840664).sum := by decide
  have hdescent : baseEnd_840664 < baseStart_840664 := by decide
  rcases family_descends (prefixWord ++ tailWord_840664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840739 : List Nat := [1, 1, 1, 4, 3, 3, 1, 1, 7]
def baseStart_840739 : Nat := 118140960795 + 840739 * 2 ^ 59
def prefixEnd_840739 : Nat := 4983230072969 + 3 ^ 40 * 840739 * 2
def baseEnd_840739 : Nat := 95934047106775852999115

theorem tailTrace_840739 : CollatzResearch.WordTrace tailWord_840739 prefixEnd_840739 95934047106775852999115 := by
  unfold tailWord_840739
  simp only [CollatzResearch.WordTrace]
  refine ⟨30664270501153664634781271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20442847000769109756520847 30664270501153664634781271)
  ·
    refine ⟨45996405751730496952171907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30664270501153664634781271 45996405751730496952171907)
    ·
      refine ⟨68994608627595745428257861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45996405751730496952171907 68994608627595745428257861)
      ·
        refine ⟨12936489117674202267798349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68994608627595745428257861 12936489117674202267798349)
        ·
          refine ⟨4851183419127825850424381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12936489117674202267798349 4851183419127825850424381)
          ·
            refine ⟨1819193782172934693909143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4851183419127825850424381 1819193782172934693909143)
            ·
              refine ⟨2728790673259402040863715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1819193782172934693909143 2728790673259402040863715)
              ·
                refine ⟨4093186009889103061295573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2728790673259402040863715 4093186009889103061295573)
                ·
                  refine ⟨95934047106775852999115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4093186009889103061295573 95934047106775852999115)
                  ·
                    rfl

theorem cell22_840739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 7].length) (baseStart_840739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840739 prefixEnd_840739 := by exact prefixLift 840739
  have htrace : WordTrace (prefixWord ++ tailWord_840739) baseStart_840739 baseEnd_840739 := by
    simpa [prefixWord, tailWord_840739, baseEnd_840739] using wordTrace_append hprefix tailTrace_840739
  have hstable : (prefixWord ++ tailWord_840739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840739).length < 2 ^ (prefixWord ++ tailWord_840739).sum := by decide
  have hdescent : baseEnd_840739 < baseStart_840739 := by decide
  rcases family_descends (prefixWord ++ tailWord_840739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840743 : List Nat := [1, 1, 7, 1, 1, 1, 1, 3, 3, 3]
def baseStart_840743 : Nat := 118140960795 + 840743 * 2 ^ 59
def prefixEnd_840743 : Nat := 4983230072969 + 3 ^ 40 * 840743 * 2
def baseEnd_840743 : Nat := 287803510602072881897333

theorem tailTrace_840743 : CollatzResearch.WordTrace tailWord_840743 prefixEnd_840743 287803510602072881897333 := by
  unfold tailWord_840743
  simp only [CollatzResearch.WordTrace]
  refine ⟨30664416393139173317926883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20442944262092782211951255 30664416393139173317926883)
  ·
    refine ⟨45996624589708759976890325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30664416393139173317926883 45996624589708759976890325)
    ·
      refine ⟨1078045888821299061958367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 45996624589708759976890325 1078045888821299061958367)
      ·
        refine ⟨1617068833231948592937551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1078045888821299061958367 1617068833231948592937551)
        ·
          refine ⟨2425603249847922889406327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1617068833231948592937551 2425603249847922889406327)
          ·
            refine ⟨3638404874771884334109491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2425603249847922889406327 3638404874771884334109491)
            ·
              refine ⟨5457607312157826501164237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3638404874771884334109491 5457607312157826501164237)
              ·
                refine ⟨2046602742059184937936589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5457607312157826501164237 2046602742059184937936589)
                ·
                  refine ⟨767476028272194351726221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2046602742059184937936589 767476028272194351726221)
                  ·
                    refine ⟨287803510602072881897333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 767476028272194351726221 287803510602072881897333)
                    ·
                      rfl

theorem cell22_840743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_840743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840743 prefixEnd_840743 := by exact prefixLift 840743
  have htrace : WordTrace (prefixWord ++ tailWord_840743) baseStart_840743 baseEnd_840743 := by
    simpa [prefixWord, tailWord_840743, baseEnd_840743] using wordTrace_append hprefix tailTrace_840743
  have hstable : (prefixWord ++ tailWord_840743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840743).length < 2 ^ (prefixWord ++ tailWord_840743).sum := by decide
  have hdescent : baseEnd_840743 < baseStart_840743 := by decide
  rcases family_descends (prefixWord ++ tailWord_840743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840754 : List Nat := [3, 2, 1, 1, 2, 2, 1, 3, 2, 5]
def baseStart_840754 : Nat := 118140960795 + 840754 * 2 ^ 59
def prefixEnd_840754 : Nat := 4983230072969 + 3 ^ 40 * 840754 * 2
def baseEnd_840754 : Nat := 287807276126872519872299

theorem tailTrace_840754 : CollatzResearch.WordTrace tailWord_840754 prefixEnd_840754 287807276126872519872299 := by
  unfold tailWord_840754
  simp only [CollatzResearch.WordTrace]
  refine ⟨7666204399024830549144329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20443211730732881464384877 7666204399024830549144329)
  ·
    refine ⟨5749653299268622911858247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7666204399024830549144329 5749653299268622911858247)
    ·
      refine ⟨8624479948902934367787371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5749653299268622911858247 8624479948902934367787371)
      ·
        refine ⟨12936719923354401551681057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8624479948902934367787371 12936719923354401551681057)
        ·
          refine ⟨9702539942515801163760793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12936719923354401551681057 9702539942515801163760793)
          ·
            refine ⟨7276904956886850872820595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9702539942515801163760793 7276904956886850872820595)
            ·
              refine ⟨10915357435330276309230893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7276904956886850872820595 10915357435330276309230893)
              ·
                refine ⟨4093259038248853615961585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10915357435330276309230893 4093259038248853615961585)
                ·
                  refine ⟨3069944278686640211971189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4093259038248853615961585 3069944278686640211971189)
                  ·
                    refine ⟨287807276126872519872299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3069944278686640211971189 287807276126872519872299)
                    ·
                      rfl

theorem cell22_840754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_840754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840754 prefixEnd_840754 := by exact prefixLift 840754
  have htrace : WordTrace (prefixWord ++ tailWord_840754) baseStart_840754 baseEnd_840754 := by
    simpa [prefixWord, tailWord_840754, baseEnd_840754] using wordTrace_append hprefix tailTrace_840754
  have hstable : (prefixWord ++ tailWord_840754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840754).length < 2 ^ (prefixWord ++ tailWord_840754).sum := by decide
  have hdescent : baseEnd_840754 < baseStart_840754 := by decide
  rcases family_descends (prefixWord ++ tailWord_840754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840801 : List Nat := [1, 2, 3, 1, 1, 2, 2, 6, 4]
def baseStart_840801 : Nat := 118140960795 + 840801 * 2 ^ 59
def prefixEnd_840801 : Nat := 4983230072969 + 3 ^ 40 * 840801 * 2
def baseEnd_840801 : Nat := 95941121729126687982385

theorem tailTrace_840801 : CollatzResearch.WordTrace tailWord_840801 prefixEnd_840801 95941121729126687982385 := by
  unfold tailWord_840801
  simp only [CollatzResearch.WordTrace]
  refine ⟨30666531826929049223538257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20444354551286032815692171 30666531826929049223538257)
  ·
    refine ⟨22999898870196786917653693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30666531826929049223538257 22999898870196786917653693)
    ·
      refine ⟨8624962076323795094120135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22999898870196786917653693 8624962076323795094120135)
      ·
        refine ⟨12937443114485692641180203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8624962076323795094120135 12937443114485692641180203)
        ·
          refine ⟨19406164671728538961770305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12937443114485692641180203 19406164671728538961770305)
          ·
            refine ⟨14554623503796404221327729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19406164671728538961770305 14554623503796404221327729)
            ·
              refine ⟨10915967627847303165995797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14554623503796404221327729 10915967627847303165995797)
              ·
                refine ⟨511685982555342335906053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10915967627847303165995797 511685982555342335906053)
                ·
                  refine ⟨95941121729126687982385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 511685982555342335906053 95941121729126687982385)
                  ·
                    rfl

theorem cell22_840801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6, 4].length) (baseStart_840801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840801 prefixEnd_840801 := by exact prefixLift 840801
  have htrace : WordTrace (prefixWord ++ tailWord_840801) baseStart_840801 baseEnd_840801 := by
    simpa [prefixWord, tailWord_840801, baseEnd_840801] using wordTrace_append hprefix tailTrace_840801
  have hstable : (prefixWord ++ tailWord_840801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840801).length < 2 ^ (prefixWord ++ tailWord_840801).sum := by decide
  have hdescent : baseEnd_840801 < baseStart_840801 := by decide
  rcases family_descends (prefixWord ++ tailWord_840801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840829 : List Nat := [1, 4, 1, 1, 3, 1, 1, 10]
def baseStart_840829 : Nat := 118140960795 + 840829 * 2 ^ 59
def prefixEnd_840829 : Nat := 4983230072969 + 3 ^ 40 * 840829 * 2
def baseEnd_840829 : Nat := 31981438906621924916341

theorem tailTrace_840829 : CollatzResearch.WordTrace tailWord_840829 prefixEnd_840829 31981438906621924916341 := by
  unfold tailWord_840829
  simp only [CollatzResearch.WordTrace]
  refine ⟨30667553070827610005557541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20445035380551740003705027 30667553070827610005557541)
  ·
    refine ⟨5750166200780176876042039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30667553070827610005557541 5750166200780176876042039)
    ·
      refine ⟨8625249301170265314063059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5750166200780176876042039 8625249301170265314063059)
      ·
        refine ⟨12937873951755397971094589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8625249301170265314063059 12937873951755397971094589)
        ·
          refine ⟨4851702731908274239160471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12937873951755397971094589 4851702731908274239160471)
          ·
            refine ⟨7277554097862411358740707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4851702731908274239160471 7277554097862411358740707)
            ·
              refine ⟨10916331146793617038111061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7277554097862411358740707 10916331146793617038111061)
              ·
                refine ⟨31981438906621924916341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10916331146793617038111061 31981438906621924916341)
                ·
                  rfl

theorem cell22_840829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 10].length) (baseStart_840829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840829 prefixEnd_840829 := by exact prefixLift 840829
  have htrace : WordTrace (prefixWord ++ tailWord_840829) baseStart_840829 baseEnd_840829 := by
    simpa [prefixWord, tailWord_840829, baseEnd_840829] using wordTrace_append hprefix tailTrace_840829
  have hstable : (prefixWord ++ tailWord_840829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840829).length < 2 ^ (prefixWord ++ tailWord_840829).sum := by decide
  have hdescent : baseEnd_840829 < baseStart_840829 := by decide
  rcases family_descends (prefixWord ++ tailWord_840829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840850 : List Nat := [3, 2, 3, 1, 1, 3, 2, 2, 2, 3]
def baseStart_840850 : Nat := 118140960795 + 840850 * 2 ^ 59
def prefixEnd_840850 : Nat := 4983230072969 + 3 ^ 40 * 840850 * 2
def baseEnd_840850 : Nat := 287840138888760269472005

theorem tailTrace_840850 : CollatzResearch.WordTrace tailWord_840850 prefixEnd_840850 287840138888760269472005 := by
  unfold tailWord_840850
  simp only [CollatzResearch.WordTrace]
  refine ⟨7667079750937882648018001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20445546002501020394714669 7667079750937882648018001)
  ·
    refine ⟨5750309813203411986013501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7667079750937882648018001 5750309813203411986013501)
    ·
      refine ⟨2156366179951279494755063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5750309813203411986013501 2156366179951279494755063)
      ·
        refine ⟨3234549269926919242132595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2156366179951279494755063 3234549269926919242132595)
        ·
          refine ⟨4851823904890378863198893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3234549269926919242132595 4851823904890378863198893)
          ·
            refine ⟨1819433964333892073699585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4851823904890378863198893 1819433964333892073699585)
            ·
              refine ⟨1364575473250419055274689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1819433964333892073699585 1364575473250419055274689)
              ·
                refine ⟨1023431604937814291456017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1364575473250419055274689 1023431604937814291456017)
                ·
                  refine ⟨767573703703360718592013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1023431604937814291456017 767573703703360718592013)
                  ·
                    refine ⟨287840138888760269472005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 767573703703360718592013 287840138888760269472005)
                    ·
                      rfl

theorem cell22_840850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_840850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840850 prefixEnd_840850 := by exact prefixLift 840850
  have htrace : WordTrace (prefixWord ++ tailWord_840850) baseStart_840850 baseEnd_840850 := by
    simpa [prefixWord, tailWord_840850, baseEnd_840850] using wordTrace_append hprefix tailTrace_840850
  have hstable : (prefixWord ++ tailWord_840850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840850).length < 2 ^ (prefixWord ++ tailWord_840850).sum := by decide
  have hdescent : baseEnd_840850 < baseStart_840850 := by decide
  rcases family_descends (prefixWord ++ tailWord_840850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840863 : List Nat := [1, 1, 2, 6, 2, 2, 1, 7]
def baseStart_840863 : Nat := 118140960795 + 840863 * 2 ^ 59
def prefixEnd_840863 : Nat := 4983230072969 + 3 ^ 40 * 840863 * 2
def baseEnd_840863 : Nat := 31982732117159174321885

theorem tailTrace_840863 : CollatzResearch.WordTrace tailWord_840863 prefixEnd_840863 31982732117159174321885 := by
  unfold tailWord_840863
  simp only [CollatzResearch.WordTrace]
  refine ⟨30668793152704433812295243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20445862101802955874863495 30668793152704433812295243)
  ·
    refine ⟨46003189729056650718442865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30668793152704433812295243 46003189729056650718442865)
    ·
      refine ⟨34502392296792488038832149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46003189729056650718442865 34502392296792488038832149)
      ·
        refine ⟨1617299638912147876820257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34502392296792488038832149 1617299638912147876820257)
        ·
          refine ⟨1212974729184110907615193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1617299638912147876820257 1212974729184110907615193)
          ·
            refine ⟨909731046888083180711395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1212974729184110907615193 909731046888083180711395)
            ·
              refine ⟨1364596570332124771067093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909731046888083180711395 1364596570332124771067093)
              ·
                refine ⟨31982732117159174321885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1364596570332124771067093 31982732117159174321885)
                ·
                  rfl

theorem cell22_840863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 7].length) (baseStart_840863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840863 prefixEnd_840863 := by exact prefixLift 840863
  have htrace : WordTrace (prefixWord ++ tailWord_840863) baseStart_840863 baseEnd_840863 := by
    simpa [prefixWord, tailWord_840863, baseEnd_840863] using wordTrace_append hprefix tailTrace_840863
  have hstable : (prefixWord ++ tailWord_840863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840863).length < 2 ^ (prefixWord ++ tailWord_840863).sum := by decide
  have hdescent : baseEnd_840863 < baseStart_840863 := by decide
  rcases family_descends (prefixWord ++ tailWord_840863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840906 : List Nat := [3, 1, 2, 1, 3, 2, 1, 2, 2, 5]
def baseStart_840906 : Nat := 118140960795 + 840906 * 2 ^ 59
def prefixEnd_840906 : Nat := 4983230072969 + 3 ^ 40 * 840906 * 2
def baseEnd_840906 : Nat := 287859308833194790071833

theorem tailTrace_840906 : CollatzResearch.WordTrace tailWord_840906 prefixEnd_840906 287859308833194790071833 := by
  unfold tailWord_840906
  simp only [CollatzResearch.WordTrace]
  refine ⟨7667590372887163039027643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20446907661032434770740381 7667590372887163039027643)
  ·
    refine ⟨11501385559330744558541465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7667590372887163039027643 11501385559330744558541465)
    ·
      refine ⟨8626039169498058418906099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11501385559330744558541465 8626039169498058418906099)
      ·
        refine ⟨12939058754247087628359149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8626039169498058418906099 12939058754247087628359149)
        ·
          refine ⟨4852147032842657860634681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12939058754247087628359149 4852147032842657860634681)
          ·
            refine ⟨3639110274631993395476011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4852147032842657860634681 3639110274631993395476011)
            ·
              refine ⟨5458665411947990093214017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3639110274631993395476011 5458665411947990093214017)
              ·
                refine ⟨4093999058960992569910513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5458665411947990093214017 4093999058960992569910513)
                ·
                  refine ⟨3070499294220744427432885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4093999058960992569910513 3070499294220744427432885)
                  ·
                    refine ⟨287859308833194790071833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3070499294220744427432885 287859308833194790071833)
                    ·
                      rfl

theorem cell22_840906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_840906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840906 prefixEnd_840906 := by exact prefixLift 840906
  have htrace : WordTrace (prefixWord ++ tailWord_840906) baseStart_840906 baseEnd_840906 := by
    simpa [prefixWord, tailWord_840906, baseEnd_840906] using wordTrace_append hprefix tailTrace_840906
  have hstable : (prefixWord ++ tailWord_840906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840906).length < 2 ^ (prefixWord ++ tailWord_840906).sum := by decide
  have hdescent : baseEnd_840906 < baseStart_840906 := by decide
  rcases family_descends (prefixWord ++ tailWord_840906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840936 : List Nat := [2, 1, 4, 1, 2, 1, 1, 4, 6]
def baseStart_840936 : Nat := 118140960795 + 840936 * 2 ^ 59
def prefixEnd_840936 : Nat := 4983230072969 + 3 ^ 40 * 840936 * 2
def baseEnd_840936 : Nat := 95956526148761570607247

theorem tailTrace_840936 : CollatzResearch.WordTrace tailWord_840936 prefixEnd_840936 95956526148761570607247 := by
  unfold tailWord_840936
  simp only [CollatzResearch.WordTrace]
  refine ⟨15335727840719983639851331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20447637120959978186468441 15335727840719983639851331)
  ·
    refine ⟨23003591761079975459776997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15335727840719983639851331 23003591761079975459776997)
    ·
      refine ⟨4313173455202495398708187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23003591761079975459776997 4313173455202495398708187)
      ·
        refine ⟨6469760182803743098062281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4313173455202495398708187 6469760182803743098062281)
        ·
          refine ⟨4852320137102807323546711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6469760182803743098062281 4852320137102807323546711)
          ·
            refine ⟨7278480205654210985320067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4852320137102807323546711 7278480205654210985320067)
            ·
              refine ⟨10917720308481316477980101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7278480205654210985320067 10917720308481316477980101)
              ·
                refine ⟨2047072557840246839621269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10917720308481316477980101 2047072557840246839621269)
                ·
                  refine ⟨95956526148761570607247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2047072557840246839621269 95956526148761570607247)
                  ·
                    rfl

theorem cell22_840936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 6].length) (baseStart_840936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840936 prefixEnd_840936 := by exact prefixLift 840936
  have htrace : WordTrace (prefixWord ++ tailWord_840936) baseStart_840936 baseEnd_840936 := by
    simpa [prefixWord, tailWord_840936, baseEnd_840936] using wordTrace_append hprefix tailTrace_840936
  have hstable : (prefixWord ++ tailWord_840936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840936).length < 2 ^ (prefixWord ++ tailWord_840936).sum := by decide
  have hdescent : baseEnd_840936 < baseStart_840936 := by decide
  rcases family_descends (prefixWord ++ tailWord_840936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840938 : List Nat := [3, 1, 3, 1, 1, 3, 1, 4, 1, 4]
def baseStart_840938 : Nat := 118140960795 + 840938 * 2 ^ 59
def prefixEnd_840938 : Nat := 4983230072969 + 3 ^ 40 * 840938 * 2
def baseEnd_840938 : Nat := 287870263087157373271735

theorem tailTrace_840938 : CollatzResearch.WordTrace tailWord_840938 prefixEnd_840938 287870263087157373271735 := by
  unfold tailWord_840938
  simp only [CollatzResearch.WordTrace]
  refine ⟨7667882156858180405318867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20447685751621814414183645 7667882156858180405318867)
  ·
    refine ⟨11501823235287270607978301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7667882156858180405318867 11501823235287270607978301)
    ·
      refine ⟨4313183713232726477991863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11501823235287270607978301 4313183713232726477991863)
      ·
        refine ⟨6469775569849089716987795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4313183713232726477991863 6469775569849089716987795)
        ·
          refine ⟨9704663354773634575481693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6469775569849089716987795 9704663354773634575481693)
          ·
            refine ⟨3639248758040112965805635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9704663354773634575481693 3639248758040112965805635)
            ·
              refine ⟨5458873137060169448708453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3639248758040112965805635 5458873137060169448708453)
              ·
                refine ⟨1023538713198781771632835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5458873137060169448708453 1023538713198781771632835)
                ·
                  refine ⟨1535308069798172657449253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1023538713198781771632835 1535308069798172657449253)
                  ·
                    refine ⟨287870263087157373271735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1535308069798172657449253 287870263087157373271735)
                    ·
                      rfl

theorem cell22_840938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_840938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_840938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_840938 prefixEnd_840938 := by exact prefixLift 840938
  have htrace : WordTrace (prefixWord ++ tailWord_840938) baseStart_840938 baseEnd_840938 := by
    simpa [prefixWord, tailWord_840938, baseEnd_840938] using wordTrace_append hprefix tailTrace_840938
  have hstable : (prefixWord ++ tailWord_840938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840938).length < 2 ^ (prefixWord ++ tailWord_840938).sum := by decide
  have hdescent : baseEnd_840938 < baseStart_840938 := by decide
  rcases family_descends (prefixWord ++ tailWord_840938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841000 : List Nat := [2, 1, 5, 1, 2, 2, 2, 1, 2, 4]
def baseStart_841000 : Nat := 118140960795 + 841000 * 2 ^ 59
def prefixEnd_841000 : Nat := 4983230072969 + 3 ^ 40 * 841000 * 2
def baseEnd_841000 : Nat := 287891486954209878221545

theorem tailTrace_841000 : CollatzResearch.WordTrace tailWord_841000 prefixEnd_841000 287891486954209878221545 := by
  unfold tailWord_841000
  simp only [CollatzResearch.WordTrace]
  refine ⟨15336894976604053105016227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20449193302138737473354969 15336894976604053105016227)
  ·
    refine ⟨23005342464906079657524341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15336894976604053105016227 23005342464906079657524341)
    ·
      refine ⟨2156750856084944967892907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23005342464906079657524341 2156750856084944967892907)
      ·
        refine ⟨3235126284127417451839361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2156750856084944967892907 3235126284127417451839361)
        ·
          refine ⟨2426344713095563088879521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3235126284127417451839361 2426344713095563088879521)
          ·
            refine ⟨1819758534821672316659641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2426344713095563088879521 1819758534821672316659641)
            ·
              refine ⟨1364818901116254237494731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1819758534821672316659641 1364818901116254237494731)
              ·
                refine ⟨2047228351674381356242097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1364818901116254237494731 2047228351674381356242097)
                ·
                  refine ⟨1535421263755786017181573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2047228351674381356242097 1535421263755786017181573)
                  ·
                    refine ⟨287891486954209878221545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1535421263755786017181573 287891486954209878221545)
                    ·
                      rfl

theorem cell22_841000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_841000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_841000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_841000 prefixEnd_841000 := by exact prefixLift 841000
  have htrace : WordTrace (prefixWord ++ tailWord_841000) baseStart_841000 baseEnd_841000 := by
    simpa [prefixWord, tailWord_841000, baseEnd_841000] using wordTrace_append hprefix tailTrace_841000
  have hstable : (prefixWord ++ tailWord_841000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841000).length < 2 ^ (prefixWord ++ tailWord_841000).sum := by decide
  have hdescent : baseEnd_841000 < baseStart_841000 := by decide
  rcases family_descends (prefixWord ++ tailWord_841000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841021 : List Nat := [1, 4, 1, 5, 2, 1, 2, 2, 4]
def baseStart_841021 : Nat := 118140960795 + 841021 * 2 ^ 59
def prefixEnd_841021 : Nat := 4983230072969 + 3 ^ 40 * 841021 * 2
def baseEnd_841021 : Nat := 95966225227790941148827

theorem tailTrace_841021 : CollatzResearch.WordTrace tailWord_841021 prefixEnd_841021 95966225227790941148827 := by
  unfold tailWord_841021
  simp only [CollatzResearch.WordTrace]
  refine ⟨30674555886132026796546917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20449703924088017864364611 30674555886132026796546917)
  ·
    refine ⟨5751479228649755024352547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30674555886132026796546917 5751479228649755024352547)
    ·
      refine ⟨8627218842974632536528821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5751479228649755024352547 8627218842974632536528821)
      ·
        refine ⟨808801766528871800299577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8627218842974632536528821 808801766528871800299577)
        ·
          refine ⟨606601324896653850224683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 808801766528871800299577 606601324896653850224683)
          ·
            refine ⟨909901987344980775337025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606601324896653850224683 909901987344980775337025)
            ·
              refine ⟨682426490508735581502769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 909901987344980775337025 682426490508735581502769)
              ·
                refine ⟨511819867881551686127077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 682426490508735581502769 511819867881551686127077)
                ·
                  refine ⟨95966225227790941148827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 511819867881551686127077 95966225227790941148827)
                  ·
                    rfl

theorem cell22_841021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_841021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_841021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_841021 prefixEnd_841021 := by exact prefixLift 841021
  have htrace : WordTrace (prefixWord ++ tailWord_841021) baseStart_841021 baseEnd_841021 := by
    simpa [prefixWord, tailWord_841021, baseEnd_841021] using wordTrace_append hprefix tailTrace_841021
  have hstable : (prefixWord ++ tailWord_841021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841021).length < 2 ^ (prefixWord ++ tailWord_841021).sum := by decide
  have hdescent : baseEnd_841021 < baseStart_841021 := by decide
  rcases family_descends (prefixWord ++ tailWord_841021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841058 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_841058 : Nat := 118140960795 + 841058 * 2 ^ 59
def prefixEnd_841058 : Nat := 4983230072969 + 3 ^ 40 * 841058 * 2
def baseEnd_841058 : Nat := 287911341539517060271367

theorem tailTrace_841058 : CollatzResearch.WordTrace tailWord_841058 prefixEnd_841058 287911341539517060271367 := by
  unfold tailWord_841058
  simp only [CollatzResearch.WordTrace]
  refine ⟨7668976346749495528910957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20450603591331988077095885 7668976346749495528910957)
  ·
    refine ⟨2875866130031060823341609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7668976346749495528910957 2875866130031060823341609)
    ·
      refine ⟨2156899597523295617506207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2875866130031060823341609 2156899597523295617506207)
      ·
        refine ⟨3235349396284943426259311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2156899597523295617506207 3235349396284943426259311)
        ·
          refine ⟨4853024094427415139388967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3235349396284943426259311 4853024094427415139388967)
          ·
            refine ⟨7279536141641122709083451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4853024094427415139388967 7279536141641122709083451)
            ·
              refine ⟨10919304212461684063625177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7279536141641122709083451 10919304212461684063625177)
              ·
                refine ⟨8189478159346263047718883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10919304212461684063625177 8189478159346263047718883)
                ·
                  refine ⟨12284217239019394571578325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8189478159346263047718883 12284217239019394571578325)
                  ·
                    refine ⟨287911341539517060271367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12284217239019394571578325 287911341539517060271367)
                    ·
                      rfl

theorem cell22_841058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_841058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_841058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_841058 prefixEnd_841058 := by exact prefixLift 841058
  have htrace : WordTrace (prefixWord ++ tailWord_841058) baseStart_841058 baseEnd_841058 := by
    simpa [prefixWord, tailWord_841058, baseEnd_841058] using wordTrace_append hprefix tailTrace_841058
  have hstable : (prefixWord ++ tailWord_841058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841058).length < 2 ^ (prefixWord ++ tailWord_841058).sum := by decide
  have hdescent : baseEnd_841058 < baseStart_841058 := by decide
  rcases family_descends (prefixWord ++ tailWord_841058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841064 : List Nat := [2, 1, 4, 2, 3, 1, 2, 3, 1, 3]
def baseStart_841064 : Nat := 118140960795 + 841064 * 2 ^ 59
def prefixEnd_841064 : Nat := 4983230072969 + 3 ^ 40 * 841064 * 2
def baseEnd_841064 : Nat := 287913395462135044621349

theorem tailTrace_841064 : CollatzResearch.WordTrace tailWord_841064 prefixEnd_841064 287913395462135044621349 := by
  unfold tailWord_841064
  simp only [CollatzResearch.WordTrace]
  refine ⟨15338062112488122570181123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20450749483317496760241497 15338062112488122570181123)
  ·
    refine ⟨23007093168732183855271685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15338062112488122570181123 23007093168732183855271685)
    ·
      refine ⟨4313829969137284472863441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23007093168732183855271685 4313829969137284472863441)
      ·
        refine ⟨3235372476852963354647581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4313829969137284472863441 3235372476852963354647581)
        ·
          refine ⟨1213264678819861257992843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3235372476852963354647581 1213264678819861257992843)
          ·
            refine ⟨1819897018229791886989265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1213264678819861257992843 1819897018229791886989265)
            ·
              refine ⟨1364922763672343915241949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1819897018229791886989265 1364922763672343915241949)
              ·
                refine ⟨511846036377128968215731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1364922763672343915241949 511846036377128968215731)
                ·
                  refine ⟨767769054565693452323597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 511846036377128968215731 767769054565693452323597)
                  ·
                    refine ⟨287913395462135044621349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 767769054565693452323597 287913395462135044621349)
                    ·
                      rfl

theorem cell22_841064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_841064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_841064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_841064 prefixEnd_841064 := by exact prefixLift 841064
  have htrace : WordTrace (prefixWord ++ tailWord_841064) baseStart_841064 baseEnd_841064 := by
    simpa [prefixWord, tailWord_841064, baseEnd_841064] using wordTrace_append hprefix tailTrace_841064
  have hstable : (prefixWord ++ tailWord_841064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841064).length < 2 ^ (prefixWord ++ tailWord_841064).sum := by decide
  have hdescent : baseEnd_841064 < baseStart_841064 := by decide
  rcases family_descends (prefixWord ++ tailWord_841064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841071 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 8]
def baseStart_841071 : Nat := 118140960795 + 841071 * 2 ^ 59
def prefixEnd_841071 : Nat := 4983230072969 + 3 ^ 40 * 841071 * 2
def baseEnd_841071 : Nat := 95971930568396453232109

theorem tailTrace_841071 : CollatzResearch.WordTrace tailWord_841071 prefixEnd_841071 95971930568396453232109 := by
  unfold tailWord_841071
  simp only [CollatzResearch.WordTrace]
  refine ⟨30676379535950885335867067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20450919690633923557244711 30676379535950885335867067)
  ·
    refine ⟨46014569303926328003800601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30676379535950885335867067 46014569303926328003800601)
    ·
      refine ⟨34510926977944746002850451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46014569303926328003800601 34510926977944746002850451)
      ·
        refine ⟨51766390466917119004275677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34510926977944746002850451 51766390466917119004275677)
        ·
          refine ⟨19412396425093919626603379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51766390466917119004275677 19412396425093919626603379)
          ·
            refine ⟨29118594637640879439905069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19412396425093919626603379 29118594637640879439905069)
            ·
              refine ⟨10919472989115329789964401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29118594637640879439905069 10919472989115329789964401)
              ·
                refine ⟨8189604741836497342473301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10919472989115329789964401 8189604741836497342473301)
                ·
                  refine ⟨95971930568396453232109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8189604741836497342473301 95971930568396453232109)
                  ·
                    rfl

theorem cell22_841071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 8].length) (baseStart_841071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_841071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_841071 prefixEnd_841071 := by exact prefixLift 841071
  have htrace : WordTrace (prefixWord ++ tailWord_841071) baseStart_841071 baseEnd_841071 := by
    simpa [prefixWord, tailWord_841071, baseEnd_841071] using wordTrace_append hprefix tailTrace_841071
  have hstable : (prefixWord ++ tailWord_841071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841071).length < 2 ^ (prefixWord ++ tailWord_841071).sum := by decide
  have hdescent : baseEnd_841071 < baseStart_841071 := by decide
  rcases family_descends (prefixWord ++ tailWord_841071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841077 : List Nat := [1, 3, 4, 1, 3, 2, 1, 2, 5]
def baseStart_841077 : Nat := 118140960795 + 841077 * 2 ^ 59
def prefixEnd_841077 : Nat := 4983230072969 + 3 ^ 40 * 841077 * 2
def baseEnd_841077 : Nat := 95972615209269114682103

theorem tailTrace_841077 : CollatzResearch.WordTrace tailWord_841077 prefixEnd_841077 95972615209269114682103 := by
  unfold tailWord_841077
  simp only [CollatzResearch.WordTrace]
  refine ⟨30676598373929148360585485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20451065582619432240390323 30676598373929148360585485)
  ·
    refine ⟨11503724390223430635219557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30676598373929148360585485 11503724390223430635219557)
    ·
      refine ⟨2156948323166893244103667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11503724390223430635219557 2156948323166893244103667)
      ·
        refine ⟨3235422484750339866155501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2156948323166893244103667 3235422484750339866155501)
        ·
          refine ⟨1213283431781377449808313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3235422484750339866155501 1213283431781377449808313)
          ·
            refine ⟨909962573836033087356235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1213283431781377449808313 909962573836033087356235)
            ·
              refine ⟨1364943860754049631034353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909962573836033087356235 1364943860754049631034353)
              ·
                refine ⟨1023707895565537223275765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1364943860754049631034353 1023707895565537223275765)
                ·
                  refine ⟨95972615209269114682103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1023707895565537223275765 95972615209269114682103)
                  ·
                    rfl

theorem cell22_841077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 5].length) (baseStart_841077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_841077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_841077 prefixEnd_841077 := by exact prefixLift 841077
  have htrace : WordTrace (prefixWord ++ tailWord_841077) baseStart_841077 baseEnd_841077 := by
    simpa [prefixWord, tailWord_841077, baseEnd_841077] using wordTrace_append hprefix tailTrace_841077
  have hstable : (prefixWord ++ tailWord_841077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841077).length < 2 ^ (prefixWord ++ tailWord_841077).sum := by decide
  have hdescent : baseEnd_841077 < baseStart_841077 := by decide
  rcases family_descends (prefixWord ++ tailWord_841077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841122 : List Nat := [3, 3, 1, 2, 1, 2, 3, 3, 4]
def baseStart_841122 : Nat := 118140960795 + 841122 * 2 ^ 59
def prefixEnd_841122 : Nat := 4983230072969 + 3 ^ 40 * 841122 * 2
def baseEnd_841122 : Nat := 95977750015814075557057

theorem tailTrace_841122 : CollatzResearch.WordTrace tailWord_841122 prefixEnd_841122 95977750015814075557057 := by
  unfold tailWord_841122
  simp only [CollatzResearch.WordTrace]
  refine ⟨7669559914691530261493405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20452159772510747363982413 7669559914691530261493405)
  ·
    refine ⟨2876084968009323848060027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7669559914691530261493405 2876084968009323848060027)
    ·
      refine ⟨4314127452013985772090041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2876084968009323848060027 4314127452013985772090041)
      ·
        refine ⟨3235595589010489329067531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4314127452013985772090041 3235595589010489329067531)
        ·
          refine ⟨4853393383515733993601297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3235595589010489329067531 4853393383515733993601297)
          ·
            refine ⟨3640045037636800495200973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4853393383515733993601297 3640045037636800495200973)
            ·
              refine ⟨1365016889113800185700365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3640045037636800495200973 1365016889113800185700365)
              ·
                refine ⟨511881333417675069637637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1365016889113800185700365 511881333417675069637637)
                ·
                  refine ⟨95977750015814075557057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 511881333417675069637637 95977750015814075557057)
                  ·
                    rfl

theorem cell22_841122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_841122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_841122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_841122 prefixEnd_841122 := by exact prefixLift 841122
  have htrace : WordTrace (prefixWord ++ tailWord_841122) baseStart_841122 baseEnd_841122 := by
    simpa [prefixWord, tailWord_841122, baseEnd_841122] using wordTrace_append hprefix tailTrace_841122
  have hstable : (prefixWord ++ tailWord_841122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841122).length < 2 ^ (prefixWord ++ tailWord_841122).sum := by decide
  have hdescent : baseEnd_841122 < baseStart_841122 := by decide
  rcases family_descends (prefixWord ++ tailWord_841122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841199 : List Nat := [1, 1, 2, 1, 4, 1, 6, 2, 1, 3]
def baseStart_841199 : Nat := 118140960795 + 841199 * 2 ^ 59
def prefixEnd_841199 : Nat := 4983230072969 + 3 ^ 40 * 841199 * 2
def baseEnd_841199 : Nat := 287959608721039692495935

theorem tailTrace_841199 : CollatzResearch.WordTrace tailWord_841199 prefixEnd_841199 287959608721039692495935 := by
  unfold tailWord_841199
  simp only [CollatzResearch.WordTrace]
  refine ⟨30681048079487163196526651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20454032052991442131017767 30681048079487163196526651)
  ·
    refine ⟨46021572119230744794789977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30681048079487163196526651 46021572119230744794789977)
    ·
      refine ⟨34516179089423058596092483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46021572119230744794789977 34516179089423058596092483)
      ·
        refine ⟨51774268634134587894138725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34516179089423058596092483 51774268634134587894138725)
        ·
          refine ⟨9707675368900235230151011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51774268634134587894138725 9707675368900235230151011)
          ·
            refine ⟨14561513053350352845226517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9707675368900235230151011 14561513053350352845226517)
            ·
              refine ⟨682570924375797789619993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14561513053350352845226517 682570924375797789619993)
              ·
                refine ⟨511928193281848342214995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 682570924375797789619993 511928193281848342214995)
                ·
                  refine ⟨767892289922772513322493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 511928193281848342214995 767892289922772513322493)
                  ·
                    refine ⟨287959608721039692495935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 767892289922772513322493 287959608721039692495935)
                    ·
                      rfl

theorem cell22_841199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2, 1, 3].length) (baseStart_841199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_841199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_841199 prefixEnd_841199 := by exact prefixLift 841199
  have htrace : WordTrace (prefixWord ++ tailWord_841199) baseStart_841199 baseEnd_841199 := by
    simpa [prefixWord, tailWord_841199, baseEnd_841199] using wordTrace_append hprefix tailTrace_841199
  have hstable : (prefixWord ++ tailWord_841199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841199).length < 2 ^ (prefixWord ++ tailWord_841199).sum := by decide
  have hdescent : baseEnd_841199 < baseStart_841199 := by decide
  rcases family_descends (prefixWord ++ tailWord_841199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841225 : List Nat := [1, 2, 1, 1, 3, 1, 4, 4, 1, 4]
def baseStart_841225 : Nat := 118140960795 + 841225 * 2 ^ 59
def prefixEnd_841225 : Nat := 4983230072969 + 3 ^ 40 * 841225 * 2
def baseEnd_841225 : Nat := 287968509052384291345855

theorem tailTrace_841225 : CollatzResearch.WordTrace tailWord_841225 prefixEnd_841225 287968509052384291345855 := by
  unfold tailWord_841225
  simp only [CollatzResearch.WordTrace]
  refine ⟨30681996377392969636973129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20454664251595313091315419 30681996377392969636973129)
  ·
    refine ⟨23011497283044727227729847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30681996377392969636973129 23011497283044727227729847)
    ·
      refine ⟨34517245924567090841594771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23011497283044727227729847 34517245924567090841594771)
      ·
        refine ⟨51775868886850636262392157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34517245924567090841594771 51775868886850636262392157)
        ·
          refine ⟨19415950832568988598397059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51775868886850636262392157 19415950832568988598397059)
          ·
            refine ⟨29123926248853482897595589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19415950832568988598397059 29123926248853482897595589)
            ·
              refine ⟨5460736171660028043299173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29123926248853482897595589 5460736171660028043299173)
              ·
                refine ⟨1023888032186255258118595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5460736171660028043299173 1023888032186255258118595)
                ·
                  refine ⟨1535832048279382887177893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1023888032186255258118595 1535832048279382887177893)
                  ·
                    refine ⟨287968509052384291345855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1535832048279382887177893 287968509052384291345855)
                    ·
                      rfl

theorem cell22_841225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 4].length) (baseStart_841225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_841225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_841225 prefixEnd_841225 := by exact prefixLift 841225
  have htrace : WordTrace (prefixWord ++ tailWord_841225) baseStart_841225 baseEnd_841225 := by
    simpa [prefixWord, tailWord_841225, baseEnd_841225] using wordTrace_append hprefix tailTrace_841225
  have hstable : (prefixWord ++ tailWord_841225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841225).length < 2 ^ (prefixWord ++ tailWord_841225).sum := by decide
  have hdescent : baseEnd_841225 < baseStart_841225 := by decide
  rcases family_descends (prefixWord ++ tailWord_841225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841246 : List Nat := [4, 3, 3, 1, 1, 1, 1, 1, 7]
def baseStart_841246 : Nat := 118140960795 + 841246 * 2 ^ 59
def prefixEnd_841246 : Nat := 4983230072969 + 3 ^ 40 * 841246 * 2
def baseEnd_841246 : Nat := 95991899260515745523597

theorem tailTrace_841246 : CollatzResearch.WordTrace tailWord_841246 prefixEnd_841246 95991899260515745523597 := by
  unfold tailWord_841246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3835345288789611277935949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20455174873544593482325061 3835345288789611277935949)
  ·
    refine ⟨1438254483296104229225981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3835345288789611277935949 1438254483296104229225981)
    ·
      refine ⟨539345431236039085959743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1438254483296104229225981 539345431236039085959743)
      ·
        refine ⟨809018146854058628939615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 539345431236039085959743 809018146854058628939615)
        ·
          refine ⟨1213527220281087943409423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 809018146854058628939615 1213527220281087943409423)
          ·
            refine ⟨1820290830421631915114135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1213527220281087943409423 1820290830421631915114135)
            ·
              refine ⟨2730436245632447872671203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1820290830421631915114135 2730436245632447872671203)
              ·
                refine ⟨4095654368448671809006805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2730436245632447872671203 4095654368448671809006805)
                ·
                  refine ⟨95991899260515745523597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4095654368448671809006805 95991899260515745523597)
                  ·
                    rfl

theorem cell22_841246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_841246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_841246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_841246 prefixEnd_841246 := by exact prefixLift 841246
  have htrace : WordTrace (prefixWord ++ tailWord_841246) baseStart_841246 baseEnd_841246 := by
    simpa [prefixWord, tailWord_841246, baseEnd_841246] using wordTrace_append hprefix tailTrace_841246
  have hstable : (prefixWord ++ tailWord_841246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841246).length < 2 ^ (prefixWord ++ tailWord_841246).sum := by decide
  have hdescent : baseEnd_841246 < baseStart_841246 := by decide
  rcases family_descends (prefixWord ++ tailWord_841246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841272 : List Nat := [2, 1, 2, 1, 4, 4, 1, 1, 1, 5]
def baseStart_841272 : Nat := 118140960795 + 841272 * 2 ^ 59
def prefixEnd_841272 : Nat := 4983230072969 + 3 ^ 40 * 841272 * 2
def baseEnd_841272 : Nat := 287984598112891835420711

theorem tailTrace_841272 : CollatzResearch.WordTrace tailWord_841272 prefixEnd_841272 287984598112891835420711 := by
  unfold tailWord_841272
  simp only [CollatzResearch.WordTrace]
  refine ⟨15341855304111348331967035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20455807072148464442622713 15341855304111348331967035)
  ·
    refine ⟨23012782956167022497950553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15341855304111348331967035 23012782956167022497950553)
    ·
      refine ⟨17259587217125266873462915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23012782956167022497950553 17259587217125266873462915)
      ·
        refine ⟨25889380825687900310194373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17259587217125266873462915 25889380825687900310194373)
        ·
          refine ⟨4854258904816481308161445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25889380825687900310194373 4854258904816481308161445)
          ·
            refine ⟨910173544653090245280271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4854258904816481308161445 910173544653090245280271)
            ·
              refine ⟨1365260316979635367920407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910173544653090245280271 1365260316979635367920407)
              ·
                refine ⟨2047890475469453051880611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1365260316979635367920407 2047890475469453051880611)
                ·
                  refine ⟨3071835713204179577820917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2047890475469453051880611 3071835713204179577820917)
                  ·
                    refine ⟨287984598112891835420711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3071835713204179577820917 287984598112891835420711)
                    ·
                      rfl

theorem cell22_841272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 1, 5].length) (baseStart_841272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_841272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_841272 prefixEnd_841272 := by exact prefixLift 841272
  have htrace : WordTrace (prefixWord ++ tailWord_841272) baseStart_841272 baseEnd_841272 := by
    simpa [prefixWord, tailWord_841272, baseEnd_841272] using wordTrace_append hprefix tailTrace_841272
  have hstable : (prefixWord ++ tailWord_841272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841272).length < 2 ^ (prefixWord ++ tailWord_841272).sum := by decide
  have hdescent : baseEnd_841272 < baseStart_841272 := by decide
  rcases family_descends (prefixWord ++ tailWord_841272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841368 : List Nat := [2, 1, 2, 4, 1, 4, 2, 2, 1, 3]
def baseStart_841368 : Nat := 118140960795 + 841368 * 2 ^ 59
def prefixEnd_841368 : Nat := 4983230072969 + 3 ^ 40 * 841368 * 2
def baseEnd_841368 : Nat := 288017460874779585020417

theorem tailTrace_841368 : CollatzResearch.WordTrace tailWord_841368 prefixEnd_841368 288017460874779585020417 := by
  unfold tailWord_841368
  simp only [CollatzResearch.WordTrace]
  refine ⟨15343606007937452529714379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20458141343916603372952505 15343606007937452529714379)
  ·
    refine ⟨23015409011906178794571569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15343606007937452529714379 23015409011906178794571569)
    ·
      refine ⟨17261556758929634095928677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23015409011906178794571569 17261556758929634095928677)
      ·
        refine ⟨3236541892299306392986627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17261556758929634095928677 3236541892299306392986627)
        ·
          refine ⟨4854812838448959589479941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3236541892299306392986627 4854812838448959589479941)
          ·
            refine ⟨910277407209179923027489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4854812838448959589479941 910277407209179923027489)
            ·
              refine ⟨682708055406884942270617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 910277407209179923027489 682708055406884942270617)
              ·
                refine ⟨512031041555163706702963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 682708055406884942270617 512031041555163706702963)
                ·
                  refine ⟨768046562332745560054445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 512031041555163706702963 768046562332745560054445)
                  ·
                    refine ⟨288017460874779585020417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 768046562332745560054445 288017460874779585020417)
                    ·
                      rfl

theorem cell22_841368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2, 1, 3].length) (baseStart_841368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_841368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_841368 prefixEnd_841368 := by exact prefixLift 841368
  have htrace : WordTrace (prefixWord ++ tailWord_841368) baseStart_841368 baseEnd_841368 := by
    simpa [prefixWord, tailWord_841368, baseEnd_841368] using wordTrace_append hprefix tailTrace_841368
  have hstable : (prefixWord ++ tailWord_841368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841368).length < 2 ^ (prefixWord ++ tailWord_841368).sum := by decide
  have hdescent : baseEnd_841368 < baseStart_841368 := by decide
  rcases family_descends (prefixWord ++ tailWord_841368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841377 : List Nat := [1, 2, 3, 3, 2, 1, 1, 2, 3, 4]
def baseStart_841377 : Nat := 118140960795 + 841377 * 2 ^ 59
def prefixEnd_841377 : Nat := 4983230072969 + 3 ^ 40 * 841377 * 2
def baseEnd_841377 : Nat := 288020541758706561545389

theorem tailTrace_841377 : CollatzResearch.WordTrace tailWord_841377 prefixEnd_841377 288020541758706561545389 := by
  unfold tailWord_841377
  simp only [CollatzResearch.WordTrace]
  refine ⟨30687540272842299596506385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20458360181894866397670923 30687540272842299596506385)
  ·
    refine ⟨23015655204631724697379789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30687540272842299596506385 23015655204631724697379789)
    ·
      refine ⟨8630870701736896761517421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23015655204631724697379789 8630870701736896761517421)
      ·
        refine ⟨3236576513151336285569033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8630870701736896761517421 3236576513151336285569033)
        ·
          refine ⟨2427432384863502214176775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3236576513151336285569033 2427432384863502214176775)
          ·
            refine ⟨3641148577295253321265163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2427432384863502214176775 3641148577295253321265163)
            ·
              refine ⟨5461722865942879981897745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3641148577295253321265163 5461722865942879981897745)
              ·
                refine ⟨4096292149457159986423309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5461722865942879981897745 4096292149457159986423309)
                ·
                  refine ⟨1536109556046434994908741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4096292149457159986423309 1536109556046434994908741)
                  ·
                    refine ⟨288020541758706561545389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1536109556046434994908741 288020541758706561545389)
                    ·
                      rfl

theorem cell22_841377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_841377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_841377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_841377 prefixEnd_841377 := by exact prefixLift 841377
  have htrace : WordTrace (prefixWord ++ tailWord_841377) baseStart_841377 baseEnd_841377 := by
    simpa [prefixWord, tailWord_841377, baseEnd_841377] using wordTrace_append hprefix tailTrace_841377
  have hstable : (prefixWord ++ tailWord_841377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841377).length < 2 ^ (prefixWord ++ tailWord_841377).sum := by decide
  have hdescent : baseEnd_841377 < baseStart_841377 := by decide
  rcases family_descends (prefixWord ++ tailWord_841377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841407 : List Nat := [1, 1, 2, 2, 2, 3, 2, 2, 4, 3]
def baseStart_841407 : Nat := 118140960795 + 841407 * 2 ^ 59
def prefixEnd_841407 : Nat := 4983230072969 + 3 ^ 40 * 841407 * 2
def baseEnd_841407 : Nat := 288030811371796483295297

theorem tailTrace_841407 : CollatzResearch.WordTrace tailWord_841407 prefixEnd_841407 288030811371796483295297 := by
  unfold tailWord_841407
  simp only [CollatzResearch.WordTrace]
  refine ⟨30688634462733614720098475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20459089641822409813398983 30688634462733614720098475)
  ·
    refine ⟨46032951694100422080147713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30688634462733614720098475 46032951694100422080147713)
    ·
      refine ⟨34524713770575316560110785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46032951694100422080147713 34524713770575316560110785)
      ·
        refine ⟨25893535327931487420083089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34524713770575316560110785 25893535327931487420083089)
        ·
          refine ⟨19420151495948615565062317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25893535327931487420083089 19420151495948615565062317)
          ·
            refine ⟨7282556810980730836898369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19420151495948615565062317 7282556810980730836898369)
            ·
              refine ⟨5461917608235548127673777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7282556810980730836898369 5461917608235548127673777)
              ·
                refine ⟨4096438206176661095755333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5461917608235548127673777 4096438206176661095755333)
                ·
                  refine ⟨768082163658123955454125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4096438206176661095755333 768082163658123955454125)
                  ·
                    refine ⟨288030811371796483295297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 768082163658123955454125 288030811371796483295297)
                    ·
                      rfl

theorem cell22_841407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4, 3].length) (baseStart_841407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_841407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_841407 prefixEnd_841407 := by exact prefixLift 841407
  have htrace : WordTrace (prefixWord ++ tailWord_841407) baseStart_841407 baseEnd_841407 := by
    simpa [prefixWord, tailWord_841407, baseEnd_841407] using wordTrace_append hprefix tailTrace_841407
  have hstable : (prefixWord ++ tailWord_841407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841407).length < 2 ^ (prefixWord ++ tailWord_841407).sum := by decide
  have hdescent : baseEnd_841407 < baseStart_841407 := by decide
  rcases family_descends (prefixWord ++ tailWord_841407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841422 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 4, 4]
def baseStart_841422 : Nat := 118140960795 + 841422 * 2 ^ 59
def prefixEnd_841422 : Nat := 4983230072969 + 3 ^ 40 * 841422 * 2
def baseEnd_841422 : Nat := 288035946178341444170251

theorem tailTrace_841422 : CollatzResearch.WordTrace tailWord_841422 prefixEnd_841422 288035946178341444170251 := by
  unfold tailWord_841422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3836147694709909035236815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20459454371786181521263013 3836147694709909035236815)
  ·
    refine ⟨5754221542064863552855223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3836147694709909035236815 5754221542064863552855223)
    ·
      refine ⟨8631332313097295329282835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5754221542064863552855223 8631332313097295329282835)
      ·
        refine ⟨12946998469645942993924253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8631332313097295329282835 12946998469645942993924253)
        ·
          refine ⟨4855124426117228622721595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12946998469645942993924253 4855124426117228622721595)
          ·
            refine ⟨7282686639175842934082393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4855124426117228622721595 7282686639175842934082393)
            ·
              refine ⟨5462014979381882200561795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7282686639175842934082393 5462014979381882200561795)
              ·
                refine ⟨8193022469072823300842693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5462014979381882200561795 8193022469072823300842693)
                ·
                  refine ⟨1536191712951154368908005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8193022469072823300842693 1536191712951154368908005)
                  ·
                    refine ⟨288035946178341444170251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1536191712951154368908005 288035946178341444170251)
                    ·
                      rfl

theorem cell22_841422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_841422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_841422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_841422 prefixEnd_841422 := by exact prefixLift 841422
  have htrace : WordTrace (prefixWord ++ tailWord_841422) baseStart_841422 baseEnd_841422 := by
    simpa [prefixWord, tailWord_841422, baseEnd_841422] using wordTrace_append hprefix tailTrace_841422
  have hstable : (prefixWord ++ tailWord_841422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841422).length < 2 ^ (prefixWord ++ tailWord_841422).sum := by decide
  have hdescent : baseEnd_841422 < baseStart_841422 := by decide
  rcases family_descends (prefixWord ++ tailWord_841422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841441 : List Nat := [1, 2, 3, 1, 6, 1, 1, 1, 1, 5]
def baseStart_841441 : Nat := 118140960795 + 841441 * 2 ^ 59
def prefixEnd_841441 : Nat := 4983230072969 + 3 ^ 40 * 841441 * 2
def baseEnd_841441 : Nat := 288042450266631727945193

theorem tailTrace_841441 : CollatzResearch.WordTrace tailWord_841441 prefixEnd_841441 288042450266631727945193 := by
  unfold tailWord_841441
  simp only [CollatzResearch.WordTrace]
  refine ⟨30689874544610438526836177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20459916363073625684557451 30689874544610438526836177)
  ·
    refine ⟨23017405908457828895127133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30689874544610438526836177 23017405908457828895127133)
    ·
      refine ⟨8631527215671685835672675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23017405908457828895127133 8631527215671685835672675)
      ·
        refine ⟨12947290823507528753509013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8631527215671685835672675 12947290823507528753509013)
        ·
          refine ⟨606904257351915410320735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12947290823507528753509013 606904257351915410320735)
          ·
            refine ⟨910356386027873115481103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606904257351915410320735 910356386027873115481103)
            ·
              refine ⟨1365534579041809673221655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910356386027873115481103 1365534579041809673221655)
              ·
                refine ⟨2048301868562714509832483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1365534579041809673221655 2048301868562714509832483)
                ·
                  refine ⟨3072452802844071764748725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2048301868562714509832483 3072452802844071764748725)
                  ·
                    refine ⟨288042450266631727945193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3072452802844071764748725 288042450266631727945193)
                    ·
                      rfl

theorem cell22_841441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_841441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_841441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_841441 prefixEnd_841441 := by exact prefixLift 841441
  have htrace : WordTrace (prefixWord ++ tailWord_841441) baseStart_841441 baseEnd_841441 := by
    simpa [prefixWord, tailWord_841441, baseEnd_841441] using wordTrace_append hprefix tailTrace_841441
  have hstable : (prefixWord ++ tailWord_841441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841441).length < 2 ^ (prefixWord ++ tailWord_841441).sum := by decide
  have hdescent : baseEnd_841441 < baseStart_841441 := by decide
  rcases family_descends (prefixWord ++ tailWord_841441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841460 : List Nat := [2, 6, 1, 1, 1, 3, 1, 3, 4]
def baseStart_841460 : Nat := 118140960795 + 841460 * 2 ^ 59
def prefixEnd_841460 : Nat := 4983230072969 + 3 ^ 40 * 841460 * 2
def baseEnd_841460 : Nat := 96016318118307337240045

theorem tailTrace_841460 : CollatzResearch.WordTrace tailWord_841460 prefixEnd_841460 96016318118307337240045 := by
  unfold tailWord_841460
  simp only [CollatzResearch.WordTrace]
  refine ⟨15345283765770802385888917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20460378354361069847851889 15345283765770802385888917)
  ·
    refine ⟨719310176520506361838543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15345283765770802385888917 719310176520506361838543)
    ·
      refine ⟨1078965264780759542757815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 719310176520506361838543 1078965264780759542757815)
      ·
        refine ⟨1618447897171139314136723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1078965264780759542757815 1618447897171139314136723)
        ·
          refine ⟨2427671845756708971205085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1618447897171139314136723 2427671845756708971205085)
          ·
            refine ⟨910376942158765864201907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2427671845756708971205085 910376942158765864201907)
            ·
              refine ⟨1365565413238148796302861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910376942158765864201907 1365565413238148796302861)
              ·
                refine ⟨512087029964305798613573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1365565413238148796302861 512087029964305798613573)
                ·
                  refine ⟨96016318118307337240045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 512087029964305798613573 96016318118307337240045)
                  ·
                    rfl

theorem cell22_841460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_841460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_841460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_841460 prefixEnd_841460 := by exact prefixLift 841460
  have htrace : WordTrace (prefixWord ++ tailWord_841460) baseStart_841460 baseEnd_841460 := by
    simpa [prefixWord, tailWord_841460, baseEnd_841460] using wordTrace_append hprefix tailTrace_841460
  have hstable : (prefixWord ++ tailWord_841460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841460).length < 2 ^ (prefixWord ++ tailWord_841460).sum := by decide
  have hdescent : baseEnd_841460 < baseStart_841460 := by decide
  rcases family_descends (prefixWord ++ tailWord_841460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841482 : List Nat := [3, 1, 2, 2, 1, 3, 2, 1, 7]
def baseStart_841482 : Nat := 118140960795 + 841482 * 2 ^ 59
def prefixEnd_841482 : Nat := 4983230072969 + 3 ^ 40 * 841482 * 2
def baseEnd_841482 : Nat := 96018828468173762556689

theorem tailTrace_841482 : CollatzResearch.WordTrace tailWord_841482 prefixEnd_841482 96018828468173762556689 := by
  unfold tailWord_841482
  simp only [CollatzResearch.WordTrace]
  refine ⟨7672842484365475632269675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20460913291641268352719133 7672842484365475632269675)
  ·
    refine ⟨11509263726548213448404513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7672842484365475632269675 11509263726548213448404513)
    ·
      refine ⟨8631947794911160086303385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11509263726548213448404513 8631947794911160086303385)
      ·
        refine ⟨6473960846183370064727539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8631947794911160086303385 6473960846183370064727539)
        ·
          refine ⟨9710941269275055097091309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6473960846183370064727539 9710941269275055097091309)
          ·
            refine ⟨3641602975978145661409241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9710941269275055097091309 3641602975978145661409241)
            ·
              refine ⟨2731202231983609246056931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3641602975978145661409241 2731202231983609246056931)
              ·
                refine ⟨4096803347975413869085397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2731202231983609246056931 4096803347975413869085397)
                ·
                  refine ⟨96018828468173762556689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4096803347975413869085397 96018828468173762556689)
                  ·
                    rfl

theorem cell22_841482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 7].length) (baseStart_841482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_841482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_841482 prefixEnd_841482 := by exact prefixLift 841482
  have htrace : WordTrace (prefixWord ++ tailWord_841482) baseStart_841482 baseEnd_841482 := by
    simpa [prefixWord, tailWord_841482, baseEnd_841482] using wordTrace_append hprefix tailTrace_841482
  have hstable : (prefixWord ++ tailWord_841482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841482).length < 2 ^ (prefixWord ++ tailWord_841482).sum := by decide
  have hdescent : baseEnd_841482 < baseStart_841482 := by decide
  rcases family_descends (prefixWord ++ tailWord_841482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841486 : List Nat := [4, 1, 1, 2, 1, 1, 2, 6, 1, 3]
def baseStart_841486 : Nat := 118140960795 + 841486 * 2 ^ 59
def prefixEnd_841486 : Nat := 4983230072969 + 3 ^ 40 * 841486 * 2
def baseEnd_841486 : Nat := 288057854686266610570055

theorem tailTrace_841486 : CollatzResearch.WordTrace tailWord_841486 prefixEnd_841486 288057854686266610570055 := by
  unfold tailWord_841486
  simp only [CollatzResearch.WordTrace]
  refine ⟨3836439478680926401528039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20461010552964940808149541 3836439478680926401528039)
  ·
    refine ⟨5754659218021389602292059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3836439478680926401528039 5754659218021389602292059)
    ·
      refine ⟨8631988827032084403438089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5754659218021389602292059 8631988827032084403438089)
      ·
        refine ⟨6473991620274063302578567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8631988827032084403438089 6473991620274063302578567)
        ·
          refine ⟨9710987430411094953867851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6473991620274063302578567 9710987430411094953867851)
          ·
            refine ⟨14566481145616642430801777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9710987430411094953867851 14566481145616642430801777)
            ·
              refine ⟨10924860859212481823101333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14566481145616642430801777 10924860859212481823101333)
              ·
                refine ⟨512102852775585085457875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10924860859212481823101333 512102852775585085457875)
                ·
                  refine ⟨768154279163377628186813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 512102852775585085457875 768154279163377628186813)
                  ·
                    refine ⟨288057854686266610570055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 768154279163377628186813 288057854686266610570055)
                    ·
                      rfl

theorem cell22_841486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_841486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_841486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_841486 prefixEnd_841486 := by exact prefixLift 841486
  have htrace : WordTrace (prefixWord ++ tailWord_841486) baseStart_841486 baseEnd_841486 := by
    simpa [prefixWord, tailWord_841486, baseEnd_841486] using wordTrace_append hprefix tailTrace_841486
  have hstable : (prefixWord ++ tailWord_841486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841486).length < 2 ^ (prefixWord ++ tailWord_841486).sum := by decide
  have hdescent : baseEnd_841486 < baseStart_841486 := by decide
  rcases family_descends (prefixWord ++ tailWord_841486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841610 : List Nat := [3, 1, 2, 4, 2, 1, 3, 1, 2, 3]
def baseStart_841610 : Nat := 118140960795 + 841610 * 2 ^ 59
def prefixEnd_841610 : Nat := 4983230072969 + 3 ^ 40 * 841610 * 2
def baseEnd_841610 : Nat := 288100302420371620469675

theorem tailTrace_841610 : CollatzResearch.WordTrace tailWord_841610 prefixEnd_841610 288100302420371620469675 := by
  unfold tailWord_841610
  simp only [CollatzResearch.WordTrace]
  refine ⟨7674009620249545097434571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20464025653998786926492189 7674009620249545097434571)
  ·
    refine ⟨11511014430374317646151857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7674009620249545097434571 11511014430374317646151857)
    ·
      refine ⟨8633260822780738234613893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11511014430374317646151857 8633260822780738234613893)
      ·
        refine ⟨1618736404271388418990105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8633260822780738234613893 1618736404271388418990105)
        ·
          refine ⟨1214052303203541314242579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1618736404271388418990105 1214052303203541314242579)
          ·
            refine ⟨1821078454805311971363869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1214052303203541314242579 1821078454805311971363869)
            ·
              refine ⟨682904420551991989261451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1821078454805311971363869 682904420551991989261451)
              ·
                refine ⟨1024356630827987983892177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 682904420551991989261451 1024356630827987983892177)
                ·
                  refine ⟨768267473120990987919133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1024356630827987983892177 768267473120990987919133)
                  ·
                    refine ⟨288100302420371620469675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 768267473120990987919133 288100302420371620469675)
                    ·
                      rfl

theorem cell22_841610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_841610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_841610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_841610 prefixEnd_841610 := by exact prefixLift 841610
  have htrace : WordTrace (prefixWord ++ tailWord_841610) baseStart_841610 baseEnd_841610 := by
    simpa [prefixWord, tailWord_841610, baseEnd_841610] using wordTrace_append hprefix tailTrace_841610
  have hstable : (prefixWord ++ tailWord_841610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841610).length < 2 ^ (prefixWord ++ tailWord_841610).sum := by decide
  have hdescent : baseEnd_841610 < baseStart_841610 := by decide
  rcases family_descends (prefixWord ++ tailWord_841610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841664 : List Nat := [2, 1, 1, 2, 3, 2, 2, 2, 3, 4]
def baseStart_841664 : Nat := 118140960795 + 841664 * 2 ^ 59
def prefixEnd_841664 : Nat := 4983230072969 + 3 ^ 40 * 841664 * 2
def baseEnd_841664 : Nat := 288118787723933479619509

theorem tailTrace_841664 : CollatzResearch.WordTrace tailWord_841664 prefixEnd_841664 288118787723933479619509 := by
  unfold tailWord_841664
  simp only [CollatzResearch.WordTrace]
  refine ⟨15349004011401273806102023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20465338681868365074802697 15349004011401273806102023)
  ·
    refine ⟨23023506017101910709153035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15349004011401273806102023 23023506017101910709153035)
    ·
      refine ⟨34535259025652866063729553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23023506017101910709153035 34535259025652866063729553)
      ·
        refine ⟨25901444269239649547797165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34535259025652866063729553 25901444269239649547797165)
        ·
          refine ⟨9713041600964868580423937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25901444269239649547797165 9713041600964868580423937)
          ·
            refine ⟨7284781200723651435317953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9713041600964868580423937 7284781200723651435317953)
            ·
              refine ⟨5463585900542738576488465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7284781200723651435317953 5463585900542738576488465)
              ·
                refine ⟨4097689425407053932366349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5463585900542738576488465 4097689425407053932366349)
                ·
                  refine ⟨1536633534527645224637381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4097689425407053932366349 1536633534527645224637381)
                  ·
                    refine ⟨288118787723933479619509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1536633534527645224637381 288118787723933479619509)
                    ·
                      rfl

theorem cell22_841664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 3, 4].length) (baseStart_841664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_841664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_841664 prefixEnd_841664 := by exact prefixLift 841664
  have htrace : WordTrace (prefixWord ++ tailWord_841664) baseStart_841664 baseEnd_841664 := by
    simpa [prefixWord, tailWord_841664, baseEnd_841664] using wordTrace_append hprefix tailTrace_841664
  have hstable : (prefixWord ++ tailWord_841664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841664).length < 2 ^ (prefixWord ++ tailWord_841664).sum := by decide
  have hdescent : baseEnd_841664 < baseStart_841664 := by decide
  rcases family_descends (prefixWord ++ tailWord_841664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841713 : List Nat := [1, 2, 2, 2, 5, 1, 1, 4, 4]
def baseStart_841713 : Nat := 118140960795 + 841713 * 2 ^ 59
def prefixEnd_841713 : Nat := 4983230072969 + 3 ^ 40 * 841713 * 2
def baseEnd_841713 : Nat := 96045187141771228381453

theorem tailTrace_841713 : CollatzResearch.WordTrace tailWord_841713 prefixEnd_841713 96045187141771228381453 := by
  unfold tailWord_841713
  simp only [CollatzResearch.WordTrace]
  refine ⟨30699795199625028980737793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20466530133083352653825195 30699795199625028980737793)
  ·
    refine ⟨23024846399718771735553345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30699795199625028980737793 23024846399718771735553345)
    ·
      refine ⟨17268634799789078801665009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23024846399718771735553345 17268634799789078801665009)
      ·
        refine ⟨12951476099841809101248757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17268634799789078801665009 12951476099841809101248757)
        ·
          refine ⟨1214200884360169603242071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12951476099841809101248757 1214200884360169603242071)
          ·
            refine ⟨1821301326540254404863107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1214200884360169603242071 1821301326540254404863107)
            ·
              refine ⟨2731951989810381607294661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1821301326540254404863107 2731951989810381607294661)
              ·
                refine ⟨512240998089446551367749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2731951989810381607294661 512240998089446551367749)
                ·
                  refine ⟨96045187141771228381453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 512240998089446551367749 96045187141771228381453)
                  ·
                    rfl

theorem cell22_841713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4, 4].length) (baseStart_841713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_841713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_841713 prefixEnd_841713 := by exact prefixLift 841713
  have htrace : WordTrace (prefixWord ++ tailWord_841713) baseStart_841713 baseEnd_841713 := by
    simpa [prefixWord, tailWord_841713, baseEnd_841713] using wordTrace_append hprefix tailTrace_841713
  have hstable : (prefixWord ++ tailWord_841713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841713).length < 2 ^ (prefixWord ++ tailWord_841713).sum := by decide
  have hdescent : baseEnd_841713 < baseStart_841713 := by decide
  rcases family_descends (prefixWord ++ tailWord_841713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841906 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 2, 6]
def baseStart_841906 : Nat := 118140960795 + 841906 * 2 ^ 59
def prefixEnd_841906 : Nat := 4983230072969 + 3 ^ 40 * 841906 * 2
def baseEnd_841906 : Nat := 288201629269525515068767

theorem tailTrace_841906 : CollatzResearch.WordTrace tailWord_841906 prefixEnd_841906 288201629269525515068767 := by
  unfold tailWord_841906
  simp only [CollatzResearch.WordTrace]
  refine ⟨7676708621981455735628393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20471222991950548628342381 7676708621981455735628393)
  ·
    refine ⟨5757531466486091801721295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7676708621981455735628393 5757531466486091801721295)
    ·
      refine ⟨8636297199729137702581943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5757531466486091801721295 8636297199729137702581943)
      ·
        refine ⟨12954445799593706553872915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8636297199729137702581943 12954445799593706553872915)
        ·
          refine ⟨19431668699390559830809373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12954445799593706553872915 19431668699390559830809373)
          ·
            refine ⟨7286875762271459936553515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19431668699390559830809373 7286875762271459936553515)
            ·
              refine ⟨10930313643407189904830273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7286875762271459936553515 10930313643407189904830273)
              ·
                refine ⟨8197735232555392428622705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10930313643407189904830273 8197735232555392428622705)
                ·
                  refine ⟨6148301424416544321467029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8197735232555392428622705 6148301424416544321467029)
                  ·
                    refine ⟨288201629269525515068767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6148301424416544321467029 288201629269525515068767)
                    ·
                      rfl

theorem cell22_841906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_841906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_841906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_841906 prefixEnd_841906 := by exact prefixLift 841906
  have htrace : WordTrace (prefixWord ++ tailWord_841906) baseStart_841906 baseEnd_841906 := by
    simpa [prefixWord, tailWord_841906, baseEnd_841906] using wordTrace_append hprefix tailTrace_841906
  have hstable : (prefixWord ++ tailWord_841906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841906).length < 2 ^ (prefixWord ++ tailWord_841906).sum := by decide
  have hdescent : baseEnd_841906 < baseStart_841906 := by decide
  rcases family_descends (prefixWord ++ tailWord_841906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841925 : List Nat := [1, 3, 1, 1, 1, 1, 5, 5, 1, 3]
def baseStart_841925 : Nat := 118140960795 + 841925 * 2 ^ 59
def prefixEnd_841925 : Nat := 4983230072969 + 3 ^ 40 * 841925 * 2
def baseEnd_841925 : Nat := 288208133357815798843709

theorem tailTrace_841925 : CollatzResearch.WordTrace tailWord_841925 prefixEnd_841925 288208133357815798843709 := by
  unfold tailWord_841925
  simp only [CollatzResearch.WordTrace]
  refine ⟨30707527474856989187455229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20471684983237992791636819 30707527474856989187455229)
  ·
    refine ⟨11515322803071370945295711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30707527474856989187455229 11515322803071370945295711)
    ·
      refine ⟨17272984204607056417943567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11515322803071370945295711 17272984204607056417943567)
      ·
        refine ⟨25909476306910584626915351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17272984204607056417943567 25909476306910584626915351)
        ·
          refine ⟨38864214460365876940373027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25909476306910584626915351 38864214460365876940373027)
          ·
            refine ⟨58296321690548815410559541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38864214460365876940373027 58296321690548815410559541)
            ·
              refine ⟨5465280158488951444739957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58296321690548815410559541 5465280158488951444739957)
              ·
                refine ⟨512370014858339197944371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5465280158488951444739957 512370014858339197944371)
                ·
                  refine ⟨768555022287508796916557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 512370014858339197944371 768555022287508796916557)
                  ·
                    refine ⟨288208133357815798843709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 768555022287508796916557 288208133357815798843709)
                    ·
                      rfl

theorem cell22_841925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5, 1, 3].length) (baseStart_841925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_841925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_841925 prefixEnd_841925 := by exact prefixLift 841925
  have htrace : WordTrace (prefixWord ++ tailWord_841925) baseStart_841925 baseEnd_841925 := by
    simpa [prefixWord, tailWord_841925, baseEnd_841925] using wordTrace_append hprefix tailTrace_841925
  have hstable : (prefixWord ++ tailWord_841925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841925).length < 2 ^ (prefixWord ++ tailWord_841925).sum := by decide
  have hdescent : baseEnd_841925 < baseStart_841925 := by decide
  rcases family_descends (prefixWord ++ tailWord_841925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841938 : List Nat := [3, 2, 2, 2, 1, 3, 1, 1, 7]
def baseStart_841938 : Nat := 118140960795 + 841938 * 2 ^ 59
def prefixEnd_841938 : Nat := 4983230072969 + 3 ^ 40 * 841938 * 2
def baseEnd_841938 : Nat := 96070861174496032756223

theorem tailTrace_841938 : CollatzResearch.WordTrace tailWord_841938 prefixEnd_841938 96070861174496032756223 := by
  unfold tailWord_841938
  simp only [CollatzResearch.WordTrace]
  refine ⟨7677000405952473101919617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20472001082539928271785645 7677000405952473101919617)
  ·
    refine ⟨5757750304464354826439713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7677000405952473101919617 5757750304464354826439713)
    ·
      refine ⟨4318312728348266119829785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5757750304464354826439713 4318312728348266119829785)
      ·
        refine ⟨3238734546261199589872339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4318312728348266119829785 3238734546261199589872339)
        ·
          refine ⟨4858101819391799384808509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3238734546261199589872339 4858101819391799384808509)
          ·
            refine ⟨1821788182271924769303191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4858101819391799384808509 1821788182271924769303191)
            ·
              refine ⟨2732682273407887153954787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1821788182271924769303191 2732682273407887153954787)
              ·
                refine ⟨4099023410111830730932181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2732682273407887153954787 4099023410111830730932181)
                ·
                  refine ⟨96070861174496032756223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4099023410111830730932181 96070861174496032756223)
                  ·
                    rfl

theorem cell22_841938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_841938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_841938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_841938 prefixEnd_841938 := by exact prefixLift 841938
  have htrace : WordTrace (prefixWord ++ tailWord_841938) baseStart_841938 baseEnd_841938 := by
    simpa [prefixWord, tailWord_841938, baseEnd_841938] using wordTrace_append hprefix tailTrace_841938
  have hstable : (prefixWord ++ tailWord_841938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841938).length < 2 ^ (prefixWord ++ tailWord_841938).sum := by decide
  have hdescent : baseEnd_841938 < baseStart_841938 := by decide
  rcases family_descends (prefixWord ++ tailWord_841938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841942 : List Nat := [5, 2, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_841942 : Nat := 118140960795 + 841942 * 2 ^ 59
def prefixEnd_841942 : Nat := 4983230072969 + 3 ^ 40 * 841942 * 2
def baseEnd_841942 : Nat := 288213952805233421168657

theorem tailTrace_841942 : CollatzResearch.WordTrace tailWord_841942 prefixEnd_841942 288213952805233421168657 := by
  unfold tailWord_841942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1919259219737212568176505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20472098343863600727216053 1919259219737212568176505)
  ·
    refine ⟨1439444414802909426132379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1919259219737212568176505 1439444414802909426132379)
    ·
      refine ⟨2159166622204364139198569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1439444414802909426132379 2159166622204364139198569)
      ·
        refine ⟨1619374966653273104398927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2159166622204364139198569 1619374966653273104398927)
        ·
          refine ⟨2429062449979909656598391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1619374966653273104398927 2429062449979909656598391)
          ·
            refine ⟨3643593674969864484897587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2429062449979909656598391 3643593674969864484897587)
            ·
              refine ⟨5465390512454796727346381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3643593674969864484897587 5465390512454796727346381)
              ·
                refine ⟨2049521442170548772754893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5465390512454796727346381 2049521442170548772754893)
                ·
                  refine ⟨768570540813955789783085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2049521442170548772754893 768570540813955789783085)
                  ·
                    refine ⟨288213952805233421168657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 768570540813955789783085 288213952805233421168657)
                    ·
                      rfl

theorem cell22_841942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_841942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_841942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_841942 prefixEnd_841942 := by exact prefixLift 841942
  have htrace : WordTrace (prefixWord ++ tailWord_841942) baseStart_841942 baseEnd_841942 := by
    simpa [prefixWord, tailWord_841942, baseEnd_841942] using wordTrace_append hprefix tailTrace_841942
  have hstable : (prefixWord ++ tailWord_841942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841942).length < 2 ^ (prefixWord ++ tailWord_841942).sum := by decide
  have hdescent : baseEnd_841942 < baseStart_841942 := by decide
  rcases family_descends (prefixWord ++ tailWord_841942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842011 : List Nat := [1, 1, 1, 1, 1, 1, 7, 9]
def baseStart_842011 : Nat := 118140960795 + 842011 * 2 ^ 59
def prefixEnd_842011 : Nat := 4983230072969 + 3 ^ 40 * 842011 * 2
def baseEnd_842011 : Nat := 32026396990593360132605

theorem tailTrace_842011 : CollatzResearch.WordTrace tailWord_842011 prefixEnd_842011 32026396990593360132605 := by
  unfold tailWord_842011
  simp only [CollatzResearch.WordTrace]
  refine ⟨30710664152545425875085887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20473776101696950583390591 30710664152545425875085887)
  ·
    refine ⟨46065996228818138812628831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30710664152545425875085887 46065996228818138812628831)
    ·
      refine ⟨69098994343227208218943247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46065996228818138812628831 69098994343227208218943247)
      ·
        refine ⟨103648491514840812328414871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69098994343227208218943247 103648491514840812328414871)
        ·
          refine ⟨155472737272261218492622307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103648491514840812328414871 155472737272261218492622307)
          ·
            refine ⟨233209105908391827738933461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155472737272261218492622307 233209105908391827738933461)
            ·
              refine ⟨5465838419727933462631253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 233209105908391827738933461 5465838419727933462631253)
              ·
                refine ⟨32026396990593360132605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5465838419727933462631253 32026396990593360132605)
                ·
                  rfl

theorem cell22_842011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 9].length) (baseStart_842011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842011 prefixEnd_842011 := by exact prefixLift 842011
  have htrace : WordTrace (prefixWord ++ tailWord_842011) baseStart_842011 baseEnd_842011 := by
    simpa [prefixWord, tailWord_842011, baseEnd_842011] using wordTrace_append hprefix tailTrace_842011
  have hstable : (prefixWord ++ tailWord_842011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842011).length < 2 ^ (prefixWord ++ tailWord_842011).sum := by decide
  have hdescent : baseEnd_842011 < baseStart_842011 := by decide
  rcases family_descends (prefixWord ++ tailWord_842011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842049 : List Nat := [1, 2, 5, 2, 2, 1, 2, 2, 2, 3]
def baseStart_842049 : Nat := 118140960795 + 842049 * 2 ^ 59
def prefixEnd_842049 : Nat := 4983230072969 + 3 ^ 40 * 842049 * 2
def baseEnd_842049 : Nat := 288250581091920808743329

theorem tailTrace_842049 : CollatzResearch.WordTrace tailWord_842049 prefixEnd_842049 288250581091920808743329 := by
  unfold tailWord_842049
  simp only [CollatzResearch.WordTrace]
  refine ⟨30712050126407758364969201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20474700084271838909979467 30712050126407758364969201)
  ·
    refine ⟨23034037594805818773726901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30712050126407758364969201 23034037594805818773726901)
    ·
      refine ⟨2159441024513045510036897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23034037594805818773726901 2159441024513045510036897)
      ·
        refine ⟨1619580768384784132527673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2159441024513045510036897 1619580768384784132527673)
        ·
          refine ⟨1214685576288588099395755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1619580768384784132527673 1214685576288588099395755)
          ·
            refine ⟨1822028364432882149093633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1214685576288588099395755 1822028364432882149093633)
            ·
              refine ⟨1366521273324661611820225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1822028364432882149093633 1366521273324661611820225)
              ·
                refine ⟨1024890954993496208865169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1366521273324661611820225 1024890954993496208865169)
                ·
                  refine ⟨768668216245122156648877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1024890954993496208865169 768668216245122156648877)
                  ·
                    refine ⟨288250581091920808743329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 768668216245122156648877 288250581091920808743329)
                    ·
                      rfl

theorem cell22_842049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_842049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842049 prefixEnd_842049 := by exact prefixLift 842049
  have htrace : WordTrace (prefixWord ++ tailWord_842049) baseStart_842049 baseEnd_842049 := by
    simpa [prefixWord, tailWord_842049, baseEnd_842049] using wordTrace_append hprefix tailTrace_842049
  have hstable : (prefixWord ++ tailWord_842049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842049).length < 2 ^ (prefixWord ++ tailWord_842049).sum := by decide
  have hdescent : baseEnd_842049 < baseStart_842049 := by decide
  rcases family_descends (prefixWord ++ tailWord_842049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842060 : List Nat := [2, 2, 1, 3, 2, 1, 2, 3, 3, 3]
def baseStart_842060 : Nat := 118140960795 + 842060 * 2 ^ 59
def prefixEnd_842060 : Nat := 4983230072969 + 3 ^ 40 * 842060 * 2
def baseEnd_842060 : Nat := 288254346616720446718295

theorem tailTrace_842060 : CollatzResearch.WordTrace tailWord_842060 prefixEnd_842060 288254346616720446718295 := by
  unfold tailWord_842060
  simp only [CollatzResearch.WordTrace]
  refine ⟨15356225664683953621809817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20474967552911938162413089 15356225664683953621809817)
  ·
    refine ⟨11517169248512965216357363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15356225664683953621809817 11517169248512965216357363)
    ·
      refine ⟨17275753872769447824536045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11517169248512965216357363 17275753872769447824536045)
      ·
        refine ⟨6478407702288542934201017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17275753872769447824536045 6478407702288542934201017)
        ·
          refine ⟨4858805776716407200650763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6478407702288542934201017 4858805776716407200650763)
          ·
            refine ⟨7288208665074610800976145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4858805776716407200650763 7288208665074610800976145)
            ·
              refine ⟨5466156498805958100732109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7288208665074610800976145 5466156498805958100732109)
              ·
                refine ⟨2049808687052234287774541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5466156498805958100732109 2049808687052234287774541)
                ·
                  refine ⟨768678257644587857915453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2049808687052234287774541 768678257644587857915453)
                  ·
                    refine ⟨288254346616720446718295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 768678257644587857915453 288254346616720446718295)
                    ·
                      rfl

theorem cell22_842060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 3, 3].length) (baseStart_842060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842060 prefixEnd_842060 := by exact prefixLift 842060
  have htrace : WordTrace (prefixWord ++ tailWord_842060) baseStart_842060 baseEnd_842060 := by
    simpa [prefixWord, tailWord_842060, baseEnd_842060] using wordTrace_append hprefix tailTrace_842060
  have hstable : (prefixWord ++ tailWord_842060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842060).length < 2 ^ (prefixWord ++ tailWord_842060).sum := by decide
  have hdescent : baseEnd_842060 < baseStart_842060 := by decide
  rcases family_descends (prefixWord ++ tailWord_842060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842103 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 5, 4]
def baseStart_842103 : Nat := 118140960795 + 842103 * 2 ^ 59
def prefixEnd_842103 : Nat := 4983230072969 + 3 ^ 40 * 842103 * 2
def baseEnd_842103 : Nat := 288269066395482667893163

theorem tailTrace_842103 : CollatzResearch.WordTrace tailWord_842103 prefixEnd_842103 288269066395482667893163 := by
  unfold tailWord_842103
  simp only [CollatzResearch.WordTrace]
  refine ⟨30714019668212125587434963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20476013112141417058289975 30714019668212125587434963)
  ·
    refine ⟨46071029502318188381152445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30714019668212125587434963 46071029502318188381152445)
    ·
      refine ⟨17276636063369320642932167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46071029502318188381152445 17276636063369320642932167)
      ·
        refine ⟨25914954095053980964398251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17276636063369320642932167 25914954095053980964398251)
        ·
          refine ⟨38872431142580971446597377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25914954095053980964398251 38872431142580971446597377)
          ·
            refine ⟨29154323356935728584948033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38872431142580971446597377 29154323356935728584948033)
            ·
              refine ⟨21865742517701796438711025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29154323356935728584948033 21865742517701796438711025)
              ·
                refine ⟨16399306888276347329033269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21865742517701796438711025 16399306888276347329033269)
                ·
                  refine ⟨1537435020775907562096869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16399306888276347329033269 1537435020775907562096869)
                  ·
                    refine ⟨288269066395482667893163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1537435020775907562096869 288269066395482667893163)
                    ·
                      rfl

theorem cell22_842103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_842103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842103 prefixEnd_842103 := by exact prefixLift 842103
  have htrace : WordTrace (prefixWord ++ tailWord_842103) baseStart_842103 baseEnd_842103 := by
    simpa [prefixWord, tailWord_842103, baseEnd_842103] using wordTrace_append hprefix tailTrace_842103
  have hstable : (prefixWord ++ tailWord_842103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842103).length < 2 ^ (prefixWord ++ tailWord_842103).sum := by decide
  have hdescent : baseEnd_842103 < baseStart_842103 := by decide
  rcases family_descends (prefixWord ++ tailWord_842103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842169 : List Nat := [1, 2, 1, 4, 3, 2, 3, 2, 4]
def baseStart_842169 : Nat := 118140960795 + 842169 * 2 ^ 59
def prefixEnd_842169 : Nat := 4983230072969 + 3 ^ 40 * 842169 * 2
def baseEnd_842169 : Nat := 96097219848093498580987

theorem tailTrace_842169 : CollatzResearch.WordTrace tailWord_842169 prefixEnd_842169 96097219848093498580987 := by
  unfold tailWord_842169
  simp only [CollatzResearch.WordTrace]
  refine ⟨30716426885973018859337561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20477617923982012572891707 30716426885973018859337561)
  ·
    refine ⟨23037320164479764144503171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30716426885973018859337561 23037320164479764144503171)
    ·
      refine ⟨34555980246719646216754757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23037320164479764144503171 34555980246719646216754757)
      ·
        refine ⟨6479246296259933665641517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34555980246719646216754757 6479246296259933665641517)
        ·
          refine ⟨2429717361097475124615569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6479246296259933665641517 2429717361097475124615569)
          ·
            refine ⟨1822288020823106343461677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2429717361097475124615569 1822288020823106343461677)
            ·
              refine ⟨683358007808664878798129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1822288020823106343461677 683358007808664878798129)
              ·
                refine ⟨512518505856498659098597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 683358007808664878798129 512518505856498659098597)
                ·
                  refine ⟨96097219848093498580987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 512518505856498659098597 96097219848093498580987)
                  ·
                    rfl

theorem cell22_842169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2, 4].length) (baseStart_842169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842169 prefixEnd_842169 := by exact prefixLift 842169
  have htrace : WordTrace (prefixWord ++ tailWord_842169) baseStart_842169 baseEnd_842169 := by
    simpa [prefixWord, tailWord_842169, baseEnd_842169] using wordTrace_append hprefix tailTrace_842169
  have hstable : (prefixWord ++ tailWord_842169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842169).length < 2 ^ (prefixWord ++ tailWord_842169).sum := by decide
  have hdescent : baseEnd_842169 < baseStart_842169 := by decide
  rcases family_descends (prefixWord ++ tailWord_842169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842184 : List Nat := [2, 1, 3, 1, 3, 2, 4, 1, 2, 3]
def baseStart_842184 : Nat := 118140960795 + 842184 * 2 ^ 59
def prefixEnd_842184 : Nat := 4983230072969 + 3 ^ 40 * 842184 * 2
def baseEnd_842184 : Nat := 288296794350825456617915

theorem tailTrace_842184 : CollatzResearch.WordTrace tailWord_842184 prefixEnd_842184 288296794350825456617915 := by
  unfold tailWord_842184
  simp only [CollatzResearch.WordTrace]
  refine ⟨15358486990459338210566803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20477982653945784280755737 15358486990459338210566803)
  ·
    refine ⟨23037730485689007315850205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15358486990459338210566803 23037730485689007315850205)
    ·
      refine ⟨8639148932133377743443827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23037730485689007315850205 8639148932133377743443827)
      ·
        refine ⟨12958723398200066615165741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8639148932133377743443827 12958723398200066615165741)
        ·
          refine ⟨4859521274325024980687153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12958723398200066615165741 4859521274325024980687153)
          ·
            refine ⟨3644640955743768735515365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4859521274325024980687153 3644640955743768735515365)
            ·
              refine ⟨683370179201956637909131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3644640955743768735515365 683370179201956637909131)
              ·
                refine ⟨1025055268802934956863697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 683370179201956637909131 1025055268802934956863697)
                ·
                  refine ⟨768791451602201217647773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1025055268802934956863697 768791451602201217647773)
                  ·
                    refine ⟨288296794350825456617915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 768791451602201217647773 288296794350825456617915)
                    ·
                      rfl

theorem cell22_842184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_842184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842184 prefixEnd_842184 := by exact prefixLift 842184
  have htrace : WordTrace (prefixWord ++ tailWord_842184) baseStart_842184 baseEnd_842184 := by
    simpa [prefixWord, tailWord_842184, baseEnd_842184] using wordTrace_append hprefix tailTrace_842184
  have hstable : (prefixWord ++ tailWord_842184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842184).length < 2 ^ (prefixWord ++ tailWord_842184).sum := by decide
  have hdescent : baseEnd_842184 < baseStart_842184 := by decide
  rcases family_descends (prefixWord ++ tailWord_842184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842263 : List Nat := [1, 1, 3, 6, 1, 1, 2, 3, 1, 3]
def baseStart_842263 : Nat := 118140960795 + 842263 * 2 ^ 59
def prefixEnd_842263 : Nat := 4983230072969 + 3 ^ 40 * 842263 * 2
def baseEnd_842263 : Nat := 288323837665295583892673

theorem tailTrace_842263 : CollatzResearch.WordTrace tailWord_842263 prefixEnd_842263 288323837665295583892673 := by
  unfold tailWord_842263
  simp only [CollatzResearch.WordTrace]
  refine ⟨30719855347632472913259443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20479903565088315275506295 30719855347632472913259443)
  ·
    refine ⟨46079783021448709369889165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30719855347632472913259443 46079783021448709369889165)
    ·
      refine ⟨17279918633043266013708437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46079783021448709369889165 17279918633043266013708437)
      ·
        refine ⟨809996185923903094392583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17279918633043266013708437 809996185923903094392583)
        ·
          refine ⟨1214994278885854641588875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 809996185923903094392583 1214994278885854641588875)
          ·
            refine ⟨1822491418328781962383313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1214994278885854641588875 1822491418328781962383313)
            ·
              refine ⟨1366868563746586471787485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1822491418328781962383313 1366868563746586471787485)
              ·
                refine ⟨512575711404969926920307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1366868563746586471787485 512575711404969926920307)
                ·
                  refine ⟨768863567107454890380461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 512575711404969926920307 768863567107454890380461)
                  ·
                    refine ⟨288323837665295583892673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 768863567107454890380461 288323837665295583892673)
                    ·
                      rfl

theorem cell22_842263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3, 1, 3].length) (baseStart_842263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842263 prefixEnd_842263 := by exact prefixLift 842263
  have htrace : WordTrace (prefixWord ++ tailWord_842263) baseStart_842263 baseEnd_842263 := by
    simpa [prefixWord, tailWord_842263, baseEnd_842263] using wordTrace_append hprefix tailTrace_842263
  have hstable : (prefixWord ++ tailWord_842263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842263).length < 2 ^ (prefixWord ++ tailWord_842263).sum := by decide
  have hdescent : baseEnd_842263 < baseStart_842263 := by decide
  rcases family_descends (prefixWord ++ tailWord_842263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842276 : List Nat := [2, 3, 1, 5, 1, 2, 1, 2, 5]
def baseStart_842276 : Nat := 118140960795 + 842276 * 2 ^ 59
def prefixEnd_842276 : Nat := 4983230072969 + 3 ^ 40 * 842276 * 2
def baseEnd_842276 : Nat := 96109429276989294439211

theorem tailTrace_842276 : CollatzResearch.WordTrace tailWord_842276 prefixEnd_842276 96109429276989294439211 := by
  unfold tailWord_842276
  simp only [CollatzResearch.WordTrace]
  refine ⟨15360164748292688066741341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20480219664390250755655121 15360164748292688066741341)
  ·
    refine ⟨5760061780609758025028003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15360164748292688066741341 5760061780609758025028003)
    ·
      refine ⟨8640092670914637037542005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5760061780609758025028003 8640092670914637037542005)
      ·
        refine ⟨810008687898247222269563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8640092670914637037542005 810008687898247222269563)
        ·
          refine ⟨1215013031847370833404345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810008687898247222269563 1215013031847370833404345)
          ·
            refine ⟨911259773885528125053259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1215013031847370833404345 911259773885528125053259)
            ·
              refine ⟨1366889660828292187579889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 911259773885528125053259 1366889660828292187579889)
              ·
                refine ⟨1025167245621219140684917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1366889660828292187579889 1025167245621219140684917)
                ·
                  refine ⟨96109429276989294439211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1025167245621219140684917 96109429276989294439211)
                  ·
                    rfl

theorem cell22_842276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_842276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842276 prefixEnd_842276 := by exact prefixLift 842276
  have htrace : WordTrace (prefixWord ++ tailWord_842276) baseStart_842276 baseEnd_842276 := by
    simpa [prefixWord, tailWord_842276, baseEnd_842276] using wordTrace_append hprefix tailTrace_842276
  have hstable : (prefixWord ++ tailWord_842276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842276).length < 2 ^ (prefixWord ++ tailWord_842276).sum := by decide
  have hdescent : baseEnd_842276 < baseStart_842276 := by decide
  rcases family_descends (prefixWord ++ tailWord_842276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842338 : List Nat := [3, 3, 2, 3, 2, 1, 1, 1, 6]
def baseStart_842338 : Nat := 118140960795 + 842338 * 2 ^ 59
def prefixEnd_842338 : Nat := 4983230072969 + 3 ^ 40 * 842338 * 2
def baseEnd_842338 : Nat := 96116503899340129422481

theorem tailTrace_842338 : CollatzResearch.WordTrace tailWord_842338 prefixEnd_842338 96116503899340129422481 := by
  unfold tailWord_842338
  simp only [CollatzResearch.WordTrace]
  refine ⟨7680647705590190180559917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20481727214907173814826445 7680647705590190180559917)
  ·
    refine ⟨2880242889596321317709969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7680647705590190180559917 2880242889596321317709969)
    ·
      refine ⟨2160182167197240988282477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2880242889596321317709969 2160182167197240988282477)
      ·
        refine ⟨810068312698965370605929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2160182167197240988282477 810068312698965370605929)
        ·
          refine ⟨607551234524224027954447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 810068312698965370605929 607551234524224027954447)
          ·
            refine ⟨911326851786336041931671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607551234524224027954447 911326851786336041931671)
            ·
              refine ⟨1366990277679504062897507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 911326851786336041931671 1366990277679504062897507)
              ·
                refine ⟨2050485416519256094346261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1366990277679504062897507 2050485416519256094346261)
                ·
                  refine ⟨96116503899340129422481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2050485416519256094346261 96116503899340129422481)
                  ·
                    rfl

theorem cell22_842338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_842338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842338 prefixEnd_842338 := by exact prefixLift 842338
  have htrace : WordTrace (prefixWord ++ tailWord_842338) baseStart_842338 baseEnd_842338 := by
    simpa [prefixWord, tailWord_842338, baseEnd_842338] using wordTrace_append hprefix tailTrace_842338
  have hstable : (prefixWord ++ tailWord_842338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842338).length < 2 ^ (prefixWord ++ tailWord_842338).sum := by decide
  have hdescent : baseEnd_842338 < baseStart_842338 := by decide
  rcases family_descends (prefixWord ++ tailWord_842338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842345 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 2, 6]
def baseStart_842345 : Nat := 118140960795 + 842345 * 2 ^ 59
def prefixEnd_842345 : Nat := 4983230072969 + 3 ^ 40 * 842345 * 2
def baseEnd_842345 : Nat := 288351907941074703342421

theorem tailTrace_842345 : CollatzResearch.WordTrace tailWord_842345 prefixEnd_842345 288351907941074703342421 := by
  unfold tailWord_842345
  simp only [CollatzResearch.WordTrace]
  refine ⟨30722846133335400917744489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20481897422223600611829659 30722846133335400917744489)
  ·
    refine ⟨23042134600001550688308367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30722846133335400917744489 23042134600001550688308367)
    ·
      refine ⟨34563201900002326032462551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23042134600001550688308367 34563201900002326032462551)
      ·
        refine ⟨51844802850003489048693827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34563201900002326032462551 51844802850003489048693827)
        ·
          refine ⟨77767204275005233573040741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51844802850003489048693827 77767204275005233573040741)
          ·
            refine ⟨14581350801563481294945139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77767204275005233573040741 14581350801563481294945139)
            ·
              refine ⟨21872026202345221942417709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14581350801563481294945139 21872026202345221942417709)
              ·
                refine ⟨8202009825879458228406641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21872026202345221942417709 8202009825879458228406641)
                ·
                  refine ⟨6151507369409593671304981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8202009825879458228406641 6151507369409593671304981)
                  ·
                    refine ⟨288351907941074703342421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6151507369409593671304981 288351907941074703342421)
                    ·
                      rfl

theorem cell22_842345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 6].length) (baseStart_842345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842345 prefixEnd_842345 := by exact prefixLift 842345
  have htrace : WordTrace (prefixWord ++ tailWord_842345) baseStart_842345 baseEnd_842345 := by
    simpa [prefixWord, tailWord_842345, baseEnd_842345] using wordTrace_append hprefix tailTrace_842345
  have hstable : (prefixWord ++ tailWord_842345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842345).length < 2 ^ (prefixWord ++ tailWord_842345).sum := by decide
  have hdescent : baseEnd_842345 < baseStart_842345 := by decide
  rcases family_descends (prefixWord ++ tailWord_842345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842347 : List Nat := [1, 1, 1, 1, 2, 2, 1, 7, 3, 3]
def baseStart_842347 : Nat := 118140960795 + 842347 * 2 ^ 59
def prefixEnd_842347 : Nat := 4983230072969 + 3 ^ 40 * 842347 * 2
def baseEnd_842347 : Nat := 288352592581947364792415

theorem tailTrace_842347 : CollatzResearch.WordTrace tailWord_842347 prefixEnd_842347 288352592581947364792415 := by
  unfold tailWord_842347
  simp only [CollatzResearch.WordTrace]
  refine ⟨30722919079328155259317295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20481946052885436839544863 30722919079328155259317295)
  ·
    refine ⟨46084378618992232888975943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30722919079328155259317295 46084378618992232888975943)
    ·
      refine ⟨69126567928488349333463915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46084378618992232888975943 69126567928488349333463915)
      ·
        refine ⟨103689851892732524000195873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69126567928488349333463915 103689851892732524000195873)
        ·
          refine ⟨77767388919549393000146905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103689851892732524000195873 77767388919549393000146905)
          ·
            refine ⟨58325541689662044750110179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77767388919549393000146905 58325541689662044750110179)
            ·
              refine ⟨87488312534493067125165269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58325541689662044750110179 87488312534493067125165269)
              ·
                refine ⟨2050507325027181260746061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 87488312534493067125165269 2050507325027181260746061)
                ·
                  refine ⟨768940246885192972779773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2050507325027181260746061 768940246885192972779773)
                  ·
                    refine ⟨288352592581947364792415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 768940246885192972779773 288352592581947364792415)
                    ·
                      rfl

theorem cell22_842347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3, 3].length) (baseStart_842347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842347 prefixEnd_842347 := by exact prefixLift 842347
  have htrace : WordTrace (prefixWord ++ tailWord_842347) baseStart_842347 baseEnd_842347 := by
    simpa [prefixWord, tailWord_842347, baseEnd_842347] using wordTrace_append hprefix tailTrace_842347
  have hstable : (prefixWord ++ tailWord_842347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842347).length < 2 ^ (prefixWord ++ tailWord_842347).sum := by decide
  have hdescent : baseEnd_842347 < baseStart_842347 := by decide
  rcases family_descends (prefixWord ++ tailWord_842347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842392 : List Nat := [2, 1, 2, 4, 1, 1, 2, 2, 2, 5]
def baseStart_842392 : Nat := 118140960795 + 842392 * 2 ^ 59
def prefixEnd_842392 : Nat := 4983230072969 + 3 ^ 40 * 842392 * 2
def baseEnd_842392 : Nat := 288367997001582247417277

theorem tailTrace_842392 : CollatzResearch.WordTrace tailWord_842392 prefixEnd_842392 288367997001582247417277 := by
  unfold tailWord_842392
  simp only [CollatzResearch.WordTrace]
  refine ⟨15362280182082563972352715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20483040242776751963136953 15362280182082563972352715)
  ·
    refine ⟨23043420273123845958529073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15362280182082563972352715 23043420273123845958529073)
    ·
      refine ⟨17282565204842884468896805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23043420273123845958529073 17282565204842884468896805)
      ·
        refine ⟨3240480975908040837918151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17282565204842884468896805 3240480975908040837918151)
        ·
          refine ⟨4860721463862061256877227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3240480975908040837918151 4860721463862061256877227)
          ·
            refine ⟨7291082195793091885315841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4860721463862061256877227 7291082195793091885315841)
            ·
              refine ⟨5468311646844818913986881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7291082195793091885315841 5468311646844818913986881)
              ·
                refine ⟨4101233735133614185490161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5468311646844818913986881 4101233735133614185490161)
                ·
                  refine ⟨3075925301350210639117621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4101233735133614185490161 3075925301350210639117621)
                  ·
                    refine ⟨288367997001582247417277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3075925301350210639117621 288367997001582247417277)
                    ·
                      rfl

theorem cell22_842392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_842392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842392 prefixEnd_842392 := by exact prefixLift 842392
  have htrace : WordTrace (prefixWord ++ tailWord_842392) baseStart_842392 baseEnd_842392 := by
    simpa [prefixWord, tailWord_842392, baseEnd_842392] using wordTrace_append hprefix tailTrace_842392
  have hstable : (prefixWord ++ tailWord_842392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842392).length < 2 ^ (prefixWord ++ tailWord_842392).sum := by decide
  have hdescent : baseEnd_842392 < baseStart_842392 := by decide
  rcases family_descends (prefixWord ++ tailWord_842392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842398 : List Nat := [4, 3, 1, 1, 1, 1, 3, 4, 1, 3]
def baseStart_842398 : Nat := 118140960795 + 842398 * 2 ^ 59
def prefixEnd_842398 : Nat := 4983230072969 + 3 ^ 40 * 842398 * 2
def baseEnd_842398 : Nat := 288370050924200231767259

theorem tailTrace_842398 : CollatzResearch.WordTrace tailWord_842398 prefixEnd_842398 288370050924200231767259 := by
  unfold tailWord_842398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3840597400267923871177981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20483186134762260646282565 3840597400267923871177981)
  ·
    refine ⟨1440224025100471451691743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3840597400267923871177981 1440224025100471451691743)
    ·
      refine ⟨2160336037650707177537615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1440224025100471451691743 2160336037650707177537615)
      ·
        refine ⟨3240504056476060766306423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2160336037650707177537615 3240504056476060766306423)
        ·
          refine ⟨4860756084714091149459635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3240504056476060766306423 4860756084714091149459635)
          ·
            refine ⟨7291134127071136724189453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4860756084714091149459635 7291134127071136724189453)
            ·
              refine ⟨2734175297651676271571045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7291134127071136724189453 2734175297651676271571045)
              ·
                refine ⟨512657868309689300919571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2734175297651676271571045 512657868309689300919571)
                ·
                  refine ⟨768986802464533951379357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 512657868309689300919571 768986802464533951379357)
                  ·
                    refine ⟨288370050924200231767259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 768986802464533951379357 288370050924200231767259)
                    ·
                      rfl

theorem cell22_842398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_842398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842398 prefixEnd_842398 := by exact prefixLift 842398
  have htrace : WordTrace (prefixWord ++ tailWord_842398) baseStart_842398 baseEnd_842398 := by
    simpa [prefixWord, tailWord_842398, baseEnd_842398] using wordTrace_append hprefix tailTrace_842398
  have hstable : (prefixWord ++ tailWord_842398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842398).length < 2 ^ (prefixWord ++ tailWord_842398).sum := by decide
  have hdescent : baseEnd_842398 < baseStart_842398 := by decide
  rcases family_descends (prefixWord ++ tailWord_842398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842445 : List Nat := [1, 6, 2, 1, 3, 1, 1, 2, 5]
def baseStart_842445 : Nat := 118140960795 + 842445 * 2 ^ 59
def prefixEnd_842445 : Nat := 4983230072969 + 3 ^ 40 * 842445 * 2
def baseEnd_842445 : Nat := 96128713328235925280705

theorem tailTrace_842445 : CollatzResearch.WordTrace tailWord_842445 prefixEnd_842445 96128713328235925280705 := by
  unfold tailWord_842445
  simp only [CollatzResearch.WordTrace]
  refine ⟨30726493432973117996384789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20484328955315411997589859 30726493432973117996384789)
  ·
    refine ⟨1440304379670614906080537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30726493432973117996384789 1440304379670614906080537)
    ·
      refine ⟨1080228284752961179560403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1440304379670614906080537 1080228284752961179560403)
      ·
        refine ⟨1620342427129441769340605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1080228284752961179560403 1620342427129441769340605)
        ·
          refine ⟨607628410173540663502727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1620342427129441769340605 607628410173540663502727)
          ·
            refine ⟨911442615260310995254091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607628410173540663502727 911442615260310995254091)
            ·
              refine ⟨1367163922890466492881137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 911442615260310995254091 1367163922890466492881137)
              ·
                refine ⟨1025372942167849869660853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1367163922890466492881137 1025372942167849869660853)
                ·
                  refine ⟨96128713328235925280705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1025372942167849869660853 96128713328235925280705)
                  ·
                    rfl

theorem cell22_842445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_842445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842445 prefixEnd_842445 := by exact prefixLift 842445
  have htrace : WordTrace (prefixWord ++ tailWord_842445) baseStart_842445 baseEnd_842445 := by
    simpa [prefixWord, tailWord_842445, baseEnd_842445] using wordTrace_append hprefix tailTrace_842445
  have hstable : (prefixWord ++ tailWord_842445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842445).length < 2 ^ (prefixWord ++ tailWord_842445).sum := by decide
  have hdescent : baseEnd_842445 < baseStart_842445 := by decide
  rcases family_descends (prefixWord ++ tailWord_842445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842497 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 1, 8]
def baseStart_842497 : Nat := 118140960795 + 842497 * 2 ^ 59
def prefixEnd_842497 : Nat := 4983230072969 + 3 ^ 40 * 842497 * 2
def baseEnd_842497 : Nat := 288403940647396973541955

theorem tailTrace_842497 : CollatzResearch.WordTrace tailWord_842497 prefixEnd_842497 288403940647396973541955 := by
  unfold tailWord_842497
  simp only [CollatzResearch.WordTrace]
  refine ⟨30728390028784730877277745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20485593352523153918185163 30728390028784730877277745)
  ·
    refine ⟨23046292521588548157958309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30728390028784730877277745 23046292521588548157958309)
    ·
      refine ⟨4321179847797852779617183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23046292521588548157958309 4321179847797852779617183)
      ·
        refine ⟨6481769771696779169425775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4321179847797852779617183 6481769771696779169425775)
        ·
          refine ⟨9722654657545168754138663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6481769771696779169425775 9722654657545168754138663)
          ·
            refine ⟨14583981986317753131207995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9722654657545168754138663 14583981986317753131207995)
            ·
              refine ⟨21875972979476629696811993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14583981986317753131207995 21875972979476629696811993)
              ·
                refine ⟨16406979734607472272608995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21875972979476629696811993 16406979734607472272608995)
                ·
                  refine ⟨24610469601911208408913493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16406979734607472272608995 24610469601911208408913493)
                  ·
                    refine ⟨288403940647396973541955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24610469601911208408913493 288403940647396973541955)
                    ·
                      rfl

theorem cell22_842497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_842497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842497 prefixEnd_842497 := by exact prefixLift 842497
  have htrace : WordTrace (prefixWord ++ tailWord_842497) baseStart_842497 baseEnd_842497 := by
    simpa [prefixWord, tailWord_842497, baseEnd_842497] using wordTrace_append hprefix tailTrace_842497
  have hstable : (prefixWord ++ tailWord_842497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842497).length < 2 ^ (prefixWord ++ tailWord_842497).sum := by decide
  have hdescent : baseEnd_842497 < baseStart_842497 := by decide
  rcases family_descends (prefixWord ++ tailWord_842497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842529 : List Nat := [1, 2, 3, 2, 1, 2, 3, 3, 5]
def baseStart_842529 : Nat := 118140960795 + 842529 * 2 ^ 59
def prefixEnd_842529 : Nat := 4983230072969 + 3 ^ 40 * 842529 * 2
def baseEnd_842529 : Nat := 96138298300453185580619

theorem tailTrace_842529 : CollatzResearch.WordTrace tailWord_842529 prefixEnd_842529 96138298300453185580619 := by
  unfold tailWord_842529
  simp only [CollatzResearch.WordTrace]
  refine ⟨30729557164668800342442641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20486371443112533561628427 30729557164668800342442641)
  ·
    refine ⟨23047167873501600256831981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30729557164668800342442641 23047167873501600256831981)
    ·
      refine ⟨8642687952563100096311993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23047167873501600256831981 8642687952563100096311993)
      ·
        refine ⟨6482015964422325072233995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8642687952563100096311993 6482015964422325072233995)
        ·
          refine ⟨9723023946633487608350993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6482015964422325072233995 9723023946633487608350993)
          ·
            refine ⟨7292267959975115706263245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9723023946633487608350993 7292267959975115706263245)
            ·
              refine ⟨2734600484990668389848717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7292267959975115706263245 2734600484990668389848717)
              ·
                refine ⟨1025475181871500646193269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2734600484990668389848717 1025475181871500646193269)
                ·
                  refine ⟨96138298300453185580619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1025475181871500646193269 96138298300453185580619)
                  ·
                    rfl

theorem cell22_842529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 5].length) (baseStart_842529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842529 prefixEnd_842529 := by exact prefixLift 842529
  have htrace : WordTrace (prefixWord ++ tailWord_842529) baseStart_842529 baseEnd_842529 := by
    simpa [prefixWord, tailWord_842529, baseEnd_842529] using wordTrace_append hprefix tailTrace_842529
  have hstable : (prefixWord ++ tailWord_842529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842529).length < 2 ^ (prefixWord ++ tailWord_842529).sum := by decide
  have hdescent : baseEnd_842529 < baseStart_842529 := by decide
  rcases family_descends (prefixWord ++ tailWord_842529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842587 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 4, 10]
def baseStart_842587 : Nat := 118140960795 + 842587 * 2 ^ 59
def prefixEnd_842587 : Nat := 4983230072969 + 3 ^ 40 * 842587 * 2
def baseEnd_842587 : Nat := 288434749486666738791679

theorem tailTrace_842587 : CollatzResearch.WordTrace tailWord_842587 prefixEnd_842587 288434749486666738791679 := by
  unfold tailWord_842587
  simp only [CollatzResearch.WordTrace]
  refine ⟨30731672598458676248054015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20487781732305784165369343 30731672598458676248054015)
  ·
    refine ⟨46097508897688014372081023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30731672598458676248054015 46097508897688014372081023)
    ·
      refine ⟨69146263346532021558121535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46097508897688014372081023 69146263346532021558121535)
      ·
        refine ⟨103719395019798032337182303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69146263346532021558121535 103719395019798032337182303)
        ·
          refine ⟨155579092529697048505773455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103719395019798032337182303 155579092529697048505773455)
          ·
            refine ⟨233368638794545572758660183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155579092529697048505773455 233368638794545572758660183)
            ·
              refine ⟨350052958191818359137990275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233368638794545572758660183 350052958191818359137990275)
              ·
                refine ⟨525079437287727538706985413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350052958191818359137990275 525079437287727538706985413)
                ·
                  refine ⟨98452394491448913507559765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 525079437287727538706985413 98452394491448913507559765)
                  ·
                    refine ⟨288434749486666738791679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 98452394491448913507559765 288434749486666738791679)
                    ·
                      rfl

theorem cell22_842587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 10].length) (baseStart_842587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842587 prefixEnd_842587 := by exact prefixLift 842587
  have htrace : WordTrace (prefixWord ++ tailWord_842587) baseStart_842587 baseEnd_842587 := by
    simpa [prefixWord, tailWord_842587, baseEnd_842587] using wordTrace_append hprefix tailTrace_842587
  have hstable : (prefixWord ++ tailWord_842587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842587).length < 2 ^ (prefixWord ++ tailWord_842587).sum := by decide
  have hdescent : baseEnd_842587 < baseStart_842587 := by decide
  rcases family_descends (prefixWord ++ tailWord_842587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842604 : List Nat := [2, 2, 1, 1, 4, 1, 3, 1, 1, 6]
def baseStart_842604 : Nat := 118140960795 + 842604 * 2 ^ 59
def prefixEnd_842604 : Nat := 4983230072969 + 3 ^ 40 * 842604 * 2
def baseEnd_842604 : Nat := 288440568934084361116627

theorem tailTrace_842604 : CollatzResearch.WordTrace tailWord_842604 prefixEnd_842604 288440568934084361116627 := by
  unfold tailWord_842604
  simp only [CollatzResearch.WordTrace]
  refine ⟨15366146319698544075711433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20488195092931392100948577 15366146319698544075711433)
  ·
    refine ⟨11524609739773908056783575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15366146319698544075711433 11524609739773908056783575)
    ·
      refine ⟨17286914609660862085175363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11524609739773908056783575 17286914609660862085175363)
      ·
        refine ⟨25930371914491293127763045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17286914609660862085175363 25930371914491293127763045)
        ·
          refine ⟨4861944733967117461455571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25930371914491293127763045 4861944733967117461455571)
          ·
            refine ⟨7292917100950676192183357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4861944733967117461455571 7292917100950676192183357)
            ·
              refine ⟨2734843912856503572068759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7292917100950676192183357 2734843912856503572068759)
              ·
                refine ⟨4102265869284755358103139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2734843912856503572068759 4102265869284755358103139)
                ·
                  refine ⟨6153398803927133037154709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4102265869284755358103139 6153398803927133037154709)
                  ·
                    refine ⟨288440568934084361116627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6153398803927133037154709 288440568934084361116627)
                    ·
                      rfl

theorem cell22_842604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_842604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842604 prefixEnd_842604 := by exact prefixLift 842604
  have htrace : WordTrace (prefixWord ++ tailWord_842604) baseStart_842604 baseEnd_842604 := by
    simpa [prefixWord, tailWord_842604, baseEnd_842604] using wordTrace_append hprefix tailTrace_842604
  have hstable : (prefixWord ++ tailWord_842604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842604).length < 2 ^ (prefixWord ++ tailWord_842604).sum := by decide
  have hdescent : baseEnd_842604 < baseStart_842604 := by decide
  rcases family_descends (prefixWord ++ tailWord_842604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842679 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 4, 5]
def baseStart_842679 : Nat := 118140960795 + 842679 * 2 ^ 59
def prefixEnd_842679 : Nat := 4983230072969 + 3 ^ 40 * 842679 * 2
def baseEnd_842679 : Nat := 288466242966809165491397

theorem tailTrace_842679 : CollatzResearch.WordTrace tailWord_842679 prefixEnd_842679 288466242966809165491397 := by
  unfold tailWord_842679
  simp only [CollatzResearch.WordTrace]
  refine ⟨30735028114125375960403091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20490018742750250640268727 30735028114125375960403091)
  ·
    refine ⟨46102542171188063940604637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30735028114125375960403091 46102542171188063940604637)
    ·
      refine ⟨17288453314195523977726739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46102542171188063940604637 17288453314195523977726739)
      ·
        refine ⟨25932679971293285966590109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17288453314195523977726739 25932679971293285966590109)
        ·
          refine ⟨9724754989234982237471291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25932679971293285966590109 9724754989234982237471291)
          ·
            refine ⟨14587132483852473356206937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9724754989234982237471291 14587132483852473356206937)
            ·
              refine ⟨10940349362889355017155203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14587132483852473356206937 10940349362889355017155203)
              ·
                refine ⟨16410524044334032525732805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10940349362889355017155203 16410524044334032525732805)
                ·
                  refine ⟨3076973258312631098574901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16410524044334032525732805 3076973258312631098574901)
                  ·
                    refine ⟨288466242966809165491397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3076973258312631098574901 288466242966809165491397)
                    ·
                      rfl

theorem cell22_842679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_842679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842679 prefixEnd_842679 := by exact prefixLift 842679
  have htrace : WordTrace (prefixWord ++ tailWord_842679) baseStart_842679 baseEnd_842679 := by
    simpa [prefixWord, tailWord_842679, baseEnd_842679] using wordTrace_append hprefix tailTrace_842679
  have hstable : (prefixWord ++ tailWord_842679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842679).length < 2 ^ (prefixWord ++ tailWord_842679).sum := by decide
  have hdescent : baseEnd_842679 < baseStart_842679 := by decide
  rcases family_descends (prefixWord ++ tailWord_842679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842685 : List Nat := [1, 4, 1, 2, 4, 2, 1, 1, 3, 3]
def baseStart_842685 : Nat := 118140960795 + 842685 * 2 ^ 59
def prefixEnd_842685 : Nat := 4983230072969 + 3 ^ 40 * 842685 * 2
def baseEnd_842685 : Nat := 288468296889427149841379

theorem tailTrace_842685 : CollatzResearch.WordTrace tailWord_842685 prefixEnd_842685 288468296889427149841379 := by
  unfold tailWord_842685
  simp only [CollatzResearch.WordTrace]
  refine ⟨30735246952103638985121509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20490164634735759323414339 30735246952103638985121509)
  ·
    refine ⟨5762858803519432309710283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30735246952103638985121509 5762858803519432309710283)
    ·
      refine ⟨8644288205279148464565425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5762858803519432309710283 8644288205279148464565425)
      ·
        refine ⟨6483216153959361348424069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8644288205279148464565425 6483216153959361348424069)
        ·
          refine ⟨1215603028867380252829513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6483216153959361348424069 1215603028867380252829513)
          ·
            refine ⟨911702271650535189622135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1215603028867380252829513 911702271650535189622135)
            ·
              refine ⟨1367553407475802784433203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 911702271650535189622135 1367553407475802784433203)
              ·
                refine ⟨2051330111213704176649805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1367553407475802784433203 2051330111213704176649805)
                ·
                  refine ⟨769248791705139066243677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2051330111213704176649805 769248791705139066243677)
                  ·
                    refine ⟨288468296889427149841379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 769248791705139066243677 288468296889427149841379)
                    ·
                      rfl

theorem cell22_842685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_842685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842685 prefixEnd_842685 := by exact prefixLift 842685
  have htrace : WordTrace (prefixWord ++ tailWord_842685) baseStart_842685 baseEnd_842685 := by
    simpa [prefixWord, tailWord_842685, baseEnd_842685] using wordTrace_append hprefix tailTrace_842685
  have hstable : (prefixWord ++ tailWord_842685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842685).length < 2 ^ (prefixWord ++ tailWord_842685).sum := by decide
  have hdescent : baseEnd_842685 < baseStart_842685 := by decide
  rcases family_descends (prefixWord ++ tailWord_842685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842711 : List Nat := [1, 1, 3, 2, 1, 1, 2, 6, 1, 4]
def baseStart_842711 : Nat := 118140960795 + 842711 * 2 ^ 59
def prefixEnd_842711 : Nat := 4983230072969 + 3 ^ 40 * 842711 * 2
def baseEnd_842711 : Nat := 288477197220771748691299

theorem tailTrace_842711 : CollatzResearch.WordTrace tailWord_842711 prefixEnd_842711 288477197220771748691299 := by
  unfold tailWord_842711
  simp only [CollatzResearch.WordTrace]
  refine ⟨30736195250009445425567987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20490796833339630283711991 30736195250009445425567987)
  ·
    refine ⟨46104292875014168138351981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30736195250009445425567987 46104292875014168138351981)
    ·
      refine ⟨17289109828130313051881993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46104292875014168138351981 17289109828130313051881993)
      ·
        refine ⟨12966832371097734788911495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17289109828130313051881993 12966832371097734788911495)
        ·
          refine ⟨19450248556646602183367243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12966832371097734788911495 19450248556646602183367243)
          ·
            refine ⟨29175372834969903275050865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19450248556646602183367243 29175372834969903275050865)
            ·
              refine ⟨21881529626227427456288149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29175372834969903275050865 21881529626227427456288149)
              ·
                refine ⟨1025696701229410662013507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21881529626227427456288149 1025696701229410662013507)
                ·
                  refine ⟨1538545051844115993020261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1025696701229410662013507 1538545051844115993020261)
                  ·
                    refine ⟨288477197220771748691299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1538545051844115993020261 288477197220771748691299)
                    ·
                      rfl

theorem cell22_842711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_842711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842711 prefixEnd_842711 := by exact prefixLift 842711
  have htrace : WordTrace (prefixWord ++ tailWord_842711) baseStart_842711 baseEnd_842711 := by
    simpa [prefixWord, tailWord_842711, baseEnd_842711] using wordTrace_append hprefix tailTrace_842711
  have hstable : (prefixWord ++ tailWord_842711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842711).length < 2 ^ (prefixWord ++ tailWord_842711).sum := by decide
  have hdescent : baseEnd_842711 < baseStart_842711 := by decide
  rcases family_descends (prefixWord ++ tailWord_842711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842739 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 5, 6]
def baseStart_842739 : Nat := 118140960795 + 842739 * 2 ^ 59
def prefixEnd_842739 : Nat := 4983230072969 + 3 ^ 40 * 842739 * 2
def baseEnd_842739 : Nat := 288486782192989008991213

theorem tailTrace_842739 : CollatzResearch.WordTrace tailWord_842739 prefixEnd_842739 288486782192989008991213 := by
  unfold tailWord_842739
  simp only [CollatzResearch.WordTrace]
  refine ⟨30737216493908006207587271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20491477662605337471724847 30737216493908006207587271)
  ·
    refine ⟨46105824740862009311380907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30737216493908006207587271 46105824740862009311380907)
    ·
      refine ⟨69158737111293013967071361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46105824740862009311380907 69158737111293013967071361)
      ·
        refine ⟨51869052833469760475303521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69158737111293013967071361 51869052833469760475303521)
        ·
          refine ⟨38901789625102320356477641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51869052833469760475303521 38901789625102320356477641)
          ·
            refine ⟨29176342218826740267358231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38901789625102320356477641 29176342218826740267358231)
            ·
              refine ⟨43764513328240110401037347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29176342218826740267358231 43764513328240110401037347)
              ·
                refine ⟨65646769992360165601556021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43764513328240110401037347 65646769992360165601556021)
                ·
                  refine ⟨6154384686783765525145877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65646769992360165601556021 6154384686783765525145877)
                  ·
                    refine ⟨288486782192989008991213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6154384686783765525145877 288486782192989008991213)
                    ·
                      rfl

theorem cell22_842739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 6].length) (baseStart_842739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842739 prefixEnd_842739 := by exact prefixLift 842739
  have htrace : WordTrace (prefixWord ++ tailWord_842739) baseStart_842739 baseEnd_842739 := by
    simpa [prefixWord, tailWord_842739, baseEnd_842739] using wordTrace_append hprefix tailTrace_842739
  have hstable : (prefixWord ++ tailWord_842739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842739).length < 2 ^ (prefixWord ++ tailWord_842739).sum := by decide
  have hdescent : baseEnd_842739 < baseStart_842739 := by decide
  rcases family_descends (prefixWord ++ tailWord_842739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842773 : List Nat := [1, 3, 2, 1, 4, 1, 3, 1, 2, 4]
def baseStart_842773 : Nat := 118140960795 + 842773 * 2 ^ 59
def prefixEnd_842773 : Nat := 4983230072969 + 3 ^ 40 * 842773 * 2
def baseEnd_842773 : Nat := 288498421087824253641109

theorem tailTrace_842773 : CollatzResearch.WordTrace tailWord_842773 prefixEnd_842773 288498421087824253641109 := by
  unfold tailWord_842773
  simp only [CollatzResearch.WordTrace]
  refine ⟨30738456575784830014324973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20492304383856553342883315 30738456575784830014324973)
  ·
    refine ⟨11526921215919311255371865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30738456575784830014324973 11526921215919311255371865)
    ·
      refine ⟨8645190911939483441528899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11526921215919311255371865 8645190911939483441528899)
      ·
        refine ⟨12967786367909225162293349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8645190911939483441528899 12967786367909225162293349)
        ·
          refine ⟨2431459943982979717930003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12967786367909225162293349 2431459943982979717930003)
          ·
            refine ⟨3647189915974469576895005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2431459943982979717930003 3647189915974469576895005)
            ·
              refine ⟨1367696218490426091335627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3647189915974469576895005 1367696218490426091335627)
              ·
                refine ⟨2051544327735639137003441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1367696218490426091335627 2051544327735639137003441)
                ·
                  refine ⟨1538658245801729352752581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2051544327735639137003441 1538658245801729352752581)
                  ·
                    refine ⟨288498421087824253641109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1538658245801729352752581 288498421087824253641109)
                    ·
                      rfl

theorem cell22_842773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_842773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842773 prefixEnd_842773 := by exact prefixLift 842773
  have htrace : WordTrace (prefixWord ++ tailWord_842773) baseStart_842773 baseEnd_842773 := by
    simpa [prefixWord, tailWord_842773, baseEnd_842773] using wordTrace_append hprefix tailTrace_842773
  have hstable : (prefixWord ++ tailWord_842773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842773).length < 2 ^ (prefixWord ++ tailWord_842773).sum := by decide
  have hdescent : baseEnd_842773 < baseStart_842773 := by decide
  rcases family_descends (prefixWord ++ tailWord_842773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842822 : List Nat := [6, 1, 1, 1, 1, 4, 2, 6]
def baseStart_842822 : Nat := 118140960795 + 842822 * 2 ^ 59
def prefixEnd_842822 : Nat := 4983230072969 + 3 ^ 40 * 842822 * 2
def baseEnd_842822 : Nat := 32057243865467162129551

theorem tailTrace_842822 : CollatzResearch.WordTrace tailWord_842822 prefixEnd_842822 32057243865467162129551 := by
  unfold tailWord_842822
  simp only [CollatzResearch.WordTrace]
  refine ⟨960632617268978480714335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20493495835071540921905813 960632617268978480714335)
  ·
    refine ⟨1440948925903467721071503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 960632617268978480714335 1440948925903467721071503)
    ·
      refine ⟨2161423388855201581607255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1440948925903467721071503 2161423388855201581607255)
      ·
        refine ⟨3242135083282802372410883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2161423388855201581607255 3242135083282802372410883)
        ·
          refine ⟨4863202624924203558616325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3242135083282802372410883 4863202624924203558616325)
          ·
            refine ⟨911850492173288167240561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4863202624924203558616325 911850492173288167240561)
            ·
              refine ⟨683887869129966125430421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 911850492173288167240561 683887869129966125430421)
              ·
                refine ⟨32057243865467162129551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 683887869129966125430421 32057243865467162129551)
                ·
                  rfl

theorem cell22_842822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_842822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842822 prefixEnd_842822 := by exact prefixLift 842822
  have htrace : WordTrace (prefixWord ++ tailWord_842822) baseStart_842822 baseEnd_842822 := by
    simpa [prefixWord, tailWord_842822, baseEnd_842822] using wordTrace_append hprefix tailTrace_842822
  have hstable : (prefixWord ++ tailWord_842822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842822).length < 2 ^ (prefixWord ++ tailWord_842822).sum := by decide
  have hdescent : baseEnd_842822 < baseStart_842822 := by decide
  rcases family_descends (prefixWord ++ tailWord_842822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842891 : List Nat := [1, 1, 1, 1, 4, 1, 1, 5, 1, 6]
def baseStart_842891 : Nat := 118140960795 + 842891 * 2 ^ 59
def prefixEnd_842891 : Nat := 4983230072969 + 3 ^ 40 * 842891 * 2
def baseEnd_842891 : Nat := 288538814899311279190747

theorem tailTrace_842891 : CollatzResearch.WordTrace tailWord_842891 prefixEnd_842891 288538814899311279190747 := by
  unfold tailWord_842891
  simp only [CollatzResearch.WordTrace]
  refine ⟨30742760389357336167120527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20495173592904890778080351 30742760389357336167120527)
  ·
    refine ⟨46114140584036004250680791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30742760389357336167120527 46114140584036004250680791)
    ·
      refine ⟨69171210876054006376021187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46114140584036004250680791 69171210876054006376021187)
      ·
        refine ⟨103756816314081009564031781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69171210876054006376021187 103756816314081009564031781)
        ·
          refine ⟨19454403058890189293255959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103756816314081009564031781 19454403058890189293255959)
          ·
            refine ⟨29181604588335283939883939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19454403058890189293255959 29181604588335283939883939)
            ·
              refine ⟨43772406882502925909825909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29181604588335283939883939 43772406882502925909825909)
              ·
                refine ⟨4103663145234649304046179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43772406882502925909825909 4103663145234649304046179)
                ·
                  refine ⟨6155494717851973956069269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4103663145234649304046179 6155494717851973956069269)
                  ·
                    refine ⟨288538814899311279190747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6155494717851973956069269 288538814899311279190747)
                    ·
                      rfl

theorem cell22_842891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 6].length) (baseStart_842891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_842891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_842891 prefixEnd_842891 := by exact prefixLift 842891
  have htrace : WordTrace (prefixWord ++ tailWord_842891) baseStart_842891 baseEnd_842891 := by
    simpa [prefixWord, tailWord_842891, baseEnd_842891] using wordTrace_append hprefix tailTrace_842891
  have hstable : (prefixWord ++ tailWord_842891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842891).length < 2 ^ (prefixWord ++ tailWord_842891).sum := by decide
  have hdescent : baseEnd_842891 < baseStart_842891 := by decide
  rcases family_descends (prefixWord ++ tailWord_842891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
