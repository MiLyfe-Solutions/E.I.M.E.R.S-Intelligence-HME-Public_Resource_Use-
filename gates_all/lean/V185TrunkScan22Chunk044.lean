import V185TrunkScan22Chunk043

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_395185 : List Nat := [1, 2, 2, 4, 2, 3, 1, 3, 4]
def baseStart_395185 : Nat := 118140960795 + 395185 * 2 ^ 59
def prefixEnd_395185 : Nat := 4983230072969 + 3 ^ 40 * 395185 * 2
def baseEnd_395185 : Nat := 45093300543809237904463

theorem tailTrace_395185 : CollatzResearch.WordTrace tailWord_395185 prefixEnd_395185 45093300543809237904463 := by
  unfold tailWord_395185
  simp only [CollatzResearch.WordTrace]
  refine ⟨14413581073319712069779009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9609054048879808046519339 14413581073319712069779009)
  ·
    refine ⟨10810185804989784052334257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14413581073319712069779009 10810185804989784052334257)
    ·
      refine ⟨8107639353742338039250693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10810185804989784052334257 8107639353742338039250693)
      ·
        refine ⟨1520182378826688382359505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8107639353742338039250693 1520182378826688382359505)
        ·
          refine ⟨1140136784120016286769629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1520182378826688382359505 1140136784120016286769629)
          ·
            refine ⟨427551294045006107538611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1140136784120016286769629 427551294045006107538611)
            ·
              refine ⟨641326941067509161307917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427551294045006107538611 641326941067509161307917)
              ·
                refine ⟨240497602900315935490469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 641326941067509161307917 240497602900315935490469)
                ·
                  refine ⟨45093300543809237904463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 240497602900315935490469 45093300543809237904463)
                  ·
                    rfl

theorem cell22_395185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3, 4].length) (baseStart_395185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_395185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_395185 prefixEnd_395185 := by exact prefixLift 395185
  have htrace : WordTrace (prefixWord ++ tailWord_395185) baseStart_395185 baseEnd_395185 := by
    simpa [prefixWord, tailWord_395185, baseEnd_395185] using wordTrace_append hprefix tailTrace_395185
  have hstable : (prefixWord ++ tailWord_395185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395185).length < 2 ^ (prefixWord ++ tailWord_395185).sum := by decide
  have hdescent : baseEnd_395185 < baseStart_395185 := by decide
  rcases family_descends (prefixWord ++ tailWord_395185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395198 : List Nat := [4, 2, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_395198 : Nat := 118140960795 + 395198 * 2 ^ 59
def prefixEnd_395198 : Nat := 4983230072969 + 3 ^ 40 * 395198 * 2
def baseEnd_395198 : Nat := 135284351797100013138349

theorem tailTrace_395198 : CollatzResearch.WordTrace tailWord_395198 prefixEnd_395198 135284351797100013138349 := by
  unfold tailWord_395198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1801756902784076911250281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9609370148181743526668165 1801756902784076911250281)
  ·
    refine ⟨1351317677088057683437711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1801756902784076911250281 1351317677088057683437711)
    ·
      refine ⟨2026976515632086525156567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1351317677088057683437711 2026976515632086525156567)
      ·
        refine ⟨3040464773448129787734851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2026976515632086525156567 3040464773448129787734851)
        ·
          refine ⟨4560697160172194681602277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3040464773448129787734851 4560697160172194681602277)
          ·
            refine ⟨855130717532286502800427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4560697160172194681602277 855130717532286502800427)
            ·
              refine ⟨1282696076298429754200641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 855130717532286502800427 1282696076298429754200641)
              ·
                refine ⟨962022057223822315650481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1282696076298429754200641 962022057223822315650481)
                ·
                  refine ⟨721516542917866736737861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 962022057223822315650481 721516542917866736737861)
                  ·
                    refine ⟨135284351797100013138349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 721516542917866736737861 135284351797100013138349)
                    ·
                      rfl

theorem cell22_395198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_395198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_395198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_395198 prefixEnd_395198 := by exact prefixLift 395198
  have htrace : WordTrace (prefixWord ++ tailWord_395198) baseStart_395198 baseEnd_395198 := by
    simpa [prefixWord, tailWord_395198, baseEnd_395198] using wordTrace_append hprefix tailTrace_395198
  have hstable : (prefixWord ++ tailWord_395198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395198).length < 2 ^ (prefixWord ++ tailWord_395198).sum := by decide
  have hdescent : baseEnd_395198 < baseStart_395198 := by decide
  rcases family_descends (prefixWord ++ tailWord_395198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395209 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 1, 8]
def baseStart_395209 : Nat := 118140960795 + 395209 * 2 ^ 59
def prefixEnd_395209 : Nat := 4983230072969 + 3 ^ 40 * 395209 * 2
def baseEnd_395209 : Nat := 135288117321899651113315

theorem tailTrace_395209 : CollatzResearch.WordTrace tailWord_395209 prefixEnd_395209 135288117321899651113315 := by
  unfold tailWord_395209
  simp only [CollatzResearch.WordTrace]
  refine ⟨14414456425232764168652681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9609637616821842779101787 14414456425232764168652681)
  ·
    refine ⟨10810842318924573126489511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14414456425232764168652681 10810842318924573126489511)
    ·
      refine ⟨16216263478386859689734267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10810842318924573126489511 16216263478386859689734267)
      ·
        refine ⟨24324395217580289534601401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16216263478386859689734267 24324395217580289534601401)
        ·
          refine ⟨18243296413185217150951051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24324395217580289534601401 18243296413185217150951051)
          ·
            refine ⟨27364944619777825726426577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18243296413185217150951051 27364944619777825726426577)
            ·
              refine ⟨20523708464833369294819933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27364944619777825726426577 20523708464833369294819933)
              ·
                refine ⟨7696390674312513485557475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20523708464833369294819933 7696390674312513485557475)
                ·
                  refine ⟨11544586011468770228336213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7696390674312513485557475 11544586011468770228336213)
                  ·
                    refine ⟨135288117321899651113315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11544586011468770228336213 135288117321899651113315)
                    ·
                      rfl

theorem cell22_395209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 8].length) (baseStart_395209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_395209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_395209 prefixEnd_395209 := by exact prefixLift 395209
  have htrace : WordTrace (prefixWord ++ tailWord_395209) baseStart_395209 baseEnd_395209 := by
    simpa [prefixWord, tailWord_395209, baseEnd_395209] using wordTrace_append hprefix tailTrace_395209
  have hstable : (prefixWord ++ tailWord_395209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395209).length < 2 ^ (prefixWord ++ tailWord_395209).sum := by decide
  have hdescent : baseEnd_395209 < baseStart_395209 := by decide
  rcases family_descends (prefixWord ++ tailWord_395209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395288 : List Nat := [2, 1, 2, 3, 2, 1, 2, 4, 1, 4]
def baseStart_395288 : Nat := 118140960795 + 395288 * 2 ^ 59
def prefixEnd_395288 : Nat := 4983230072969 + 3 ^ 40 * 395288 * 2
def baseEnd_395288 : Nat := 135315160636369778388073

theorem tailTrace_395288 : CollatzResearch.WordTrace tailWord_395288 prefixEnd_395288 135315160636369778388073 := by
  unfold tailWord_395288
  simp only [CollatzResearch.WordTrace]
  refine ⟨7208668895973280330389259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9611558527964373773852345 7208668895973280330389259)
  ·
    refine ⟨10813003343959920495583889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7208668895973280330389259 10813003343959920495583889)
    ·
      refine ⟨8109752507969940371687917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10813003343959920495583889 8109752507969940371687917)
      ·
        refine ⟨3041157190488727639382969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8109752507969940371687917 3041157190488727639382969)
        ·
          refine ⟨2280867892866545729537227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3041157190488727639382969 2280867892866545729537227)
          ·
            refine ⟨3421301839299818594305841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2280867892866545729537227 3421301839299818594305841)
            ·
              refine ⟨2565976379474863945729381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3421301839299818594305841 2565976379474863945729381)
              ·
                refine ⟨481120571151536989824259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2565976379474863945729381 481120571151536989824259)
                ·
                  refine ⟨721680856727305484736389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 481120571151536989824259 721680856727305484736389)
                  ·
                    refine ⟨135315160636369778388073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 721680856727305484736389 135315160636369778388073)
                    ·
                      rfl

theorem cell22_395288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_395288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_395288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_395288 prefixEnd_395288 := by exact prefixLift 395288
  have htrace : WordTrace (prefixWord ++ tailWord_395288) baseStart_395288 baseEnd_395288 := by
    simpa [prefixWord, tailWord_395288, baseEnd_395288] using wordTrace_append hprefix tailTrace_395288
  have hstable : (prefixWord ++ tailWord_395288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395288).length < 2 ^ (prefixWord ++ tailWord_395288).sum := by decide
  have hdescent : baseEnd_395288 < baseStart_395288 := by decide
  rcases family_descends (prefixWord ++ tailWord_395288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395361 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 1, 8]
def baseStart_395361 : Nat := 118140960795 + 395361 * 2 ^ 59
def prefixEnd_395361 : Nat := 4983230072969 + 3 ^ 40 * 395361 * 2
def baseEnd_395361 : Nat := 135340150028221921312849

theorem tailTrace_395361 : CollatzResearch.WordTrace tailWord_395361 prefixEnd_395361 135340150028221921312849 := by
  unfold tailWord_395361
  simp only [CollatzResearch.WordTrace]
  refine ⟨14420000320682094128185937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9613333547121396085457291 14420000320682094128185937)
  ·
    refine ⟨10815000240511570596139453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14420000320682094128185937 10815000240511570596139453)
    ·
      refine ⟨4055625090191838973552295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10815000240511570596139453 4055625090191838973552295)
      ·
        refine ⟨6083437635287758460328443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4055625090191838973552295 6083437635287758460328443)
        ·
          refine ⟨9125156452931637690492665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6083437635287758460328443 9125156452931637690492665)
          ·
            refine ⟨6843867339698728267869499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9125156452931637690492665 6843867339698728267869499)
            ·
              refine ⟨10265801009548092401804249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6843867339698728267869499 10265801009548092401804249)
              ·
                refine ⟨7699350757161069301353187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10265801009548092401804249 7699350757161069301353187)
                ·
                  refine ⟨11549026135741603952029781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7699350757161069301353187 11549026135741603952029781)
                  ·
                    refine ⟨135340150028221921312849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11549026135741603952029781 135340150028221921312849)
                    ·
                      rfl

theorem cell22_395361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_395361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_395361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_395361 prefixEnd_395361 := by exact prefixLift 395361
  have htrace : WordTrace (prefixWord ++ tailWord_395361) baseStart_395361 baseEnd_395361 := by
    simpa [prefixWord, tailWord_395361, baseEnd_395361] using wordTrace_append hprefix tailTrace_395361
  have hstable : (prefixWord ++ tailWord_395361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395361).length < 2 ^ (prefixWord ++ tailWord_395361).sum := by decide
  have hdescent : baseEnd_395361 < baseStart_395361 := by decide
  rcases family_descends (prefixWord ++ tailWord_395361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395363 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 5, 3]
def baseStart_395363 : Nat := 118140960795 + 395363 * 2 ^ 59
def prefixEnd_395363 : Nat := 4983230072969 + 3 ^ 40 * 395363 * 2
def baseEnd_395363 : Nat := 135340834669094582762843

theorem tailTrace_395363 : CollatzResearch.WordTrace tailWord_395363 prefixEnd_395363 135340834669094582762843 := by
  unfold tailWord_395363
  simp only [CollatzResearch.WordTrace]
  refine ⟨14420073266674848469758743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9613382177783232313172495 14420073266674848469758743)
  ·
    refine ⟨21630109900012272704638115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14420073266674848469758743 21630109900012272704638115)
    ·
      refine ⟨32445164850018409056957173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21630109900012272704638115 32445164850018409056957173)
      ·
        refine ⟨3041734204689225849089735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32445164850018409056957173 3041734204689225849089735)
        ·
          refine ⟨4562601307033838773634603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3041734204689225849089735 4562601307033838773634603)
          ·
            refine ⟨6843901960550758160451905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4562601307033838773634603 6843901960550758160451905)
            ·
              refine ⟨5132926470413068620338929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6843901960550758160451905 5132926470413068620338929)
              ·
                refine ⟨3849694852809801465254197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5132926470413068620338929 3849694852809801465254197)
                ·
                  refine ⟨360908892450918887367581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3849694852809801465254197 360908892450918887367581)
                  ·
                    refine ⟨135340834669094582762843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 360908892450918887367581 135340834669094582762843)
                    ·
                      rfl

theorem cell22_395363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5, 3].length) (baseStart_395363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_395363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_395363 prefixEnd_395363 := by exact prefixLift 395363
  have htrace : WordTrace (prefixWord ++ tailWord_395363) baseStart_395363 baseEnd_395363 := by
    simpa [prefixWord, tailWord_395363, baseEnd_395363] using wordTrace_append hprefix tailTrace_395363
  have hstable : (prefixWord ++ tailWord_395363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395363).length < 2 ^ (prefixWord ++ tailWord_395363).sum := by decide
  have hdescent : baseEnd_395363 < baseStart_395363 := by decide
  rcases family_descends (prefixWord ++ tailWord_395363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395470 : List Nat := [4, 1, 1, 1, 4, 1, 2, 2, 1, 5]
def baseStart_395470 : Nat := 118140960795 + 395470 * 2 ^ 59
def prefixEnd_395470 : Nat := 4983230072969 + 3 ^ 40 * 395470 * 2
def baseEnd_395470 : Nat := 135377462955781970337515

theorem tailTrace_395470 : CollatzResearch.WordTrace tailWord_395470 prefixEnd_395470 135377462955781970337515 := by
  unfold tailWord_395470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1802996984660900717987983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9615983918191470495935909 1802996984660900717987983)
  ·
    refine ⟨2704495476991351076981975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1802996984660900717987983 2704495476991351076981975)
    ·
      refine ⟨4056743215487026615472963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2704495476991351076981975 4056743215487026615472963)
      ·
        refine ⟨6085114823230539923209445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4056743215487026615472963 6085114823230539923209445)
        ·
          refine ⟨1140959029355726235601771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6085114823230539923209445 1140959029355726235601771)
          ·
            refine ⟨1711438544033589353402657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1140959029355726235601771 1711438544033589353402657)
            ·
              refine ⟨1283578908025192015051993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1711438544033589353402657 1283578908025192015051993)
              ·
                refine ⟨962684181018894011288995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1283578908025192015051993 962684181018894011288995)
                ·
                  refine ⟨1444026271528341016933493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 962684181018894011288995 1444026271528341016933493)
                  ·
                    refine ⟨135377462955781970337515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1444026271528341016933493 135377462955781970337515)
                    ·
                      rfl

theorem cell22_395470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_395470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_395470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_395470 prefixEnd_395470 := by exact prefixLift 395470
  have htrace : WordTrace (prefixWord ++ tailWord_395470) baseStart_395470 baseEnd_395470 := by
    simpa [prefixWord, tailWord_395470, baseEnd_395470] using wordTrace_append hprefix tailTrace_395470
  have hstable : (prefixWord ++ tailWord_395470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395470).length < 2 ^ (prefixWord ++ tailWord_395470).sum := by decide
  have hdescent : baseEnd_395470 < baseStart_395470 := by decide
  rcases family_descends (prefixWord ++ tailWord_395470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395474 : List Nat := [3, 2, 2, 2, 1, 4, 2, 1, 1, 4]
def baseStart_395474 : Nat := 118140960795 + 395474 * 2 ^ 59
def prefixEnd_395474 : Nat := 4983230072969 + 3 ^ 40 * 395474 * 2
def baseEnd_395474 : Nat := 135378832237527293237503

theorem tailTrace_395474 : CollatzResearch.WordTrace tailWord_395474 prefixEnd_395474 135378832237527293237503 := by
  unfold tailWord_395474
  simp only [CollatzResearch.WordTrace]
  refine ⟨3606030442318178606762369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9616081179515142951366317 3606030442318178606762369)
  ·
    refine ⟨2704522831738633955071777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3606030442318178606762369 2704522831738633955071777)
    ·
      refine ⟨2028392123803975466303833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2704522831738633955071777 2028392123803975466303833)
      ·
        refine ⟨1521294092852981599727875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2028392123803975466303833 1521294092852981599727875)
        ·
          refine ⟨2281941139279472399591813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1521294092852981599727875 2281941139279472399591813)
          ·
            refine ⟨427863963614901074923465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2281941139279472399591813 427863963614901074923465)
            ·
              refine ⟨320897972711175806192599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 427863963614901074923465 320897972711175806192599)
              ·
                refine ⟨481346959066763709288899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320897972711175806192599 481346959066763709288899)
                ·
                  refine ⟨722020438600145563933349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 481346959066763709288899 722020438600145563933349)
                  ·
                    refine ⟨135378832237527293237503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 722020438600145563933349 135378832237527293237503)
                    ·
                      rfl

theorem cell22_395474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_395474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_395474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_395474 prefixEnd_395474 := by exact prefixLift 395474
  have htrace : WordTrace (prefixWord ++ tailWord_395474) baseStart_395474 baseEnd_395474 := by
    simpa [prefixWord, tailWord_395474, baseEnd_395474] using wordTrace_append hprefix tailTrace_395474
  have hstable : (prefixWord ++ tailWord_395474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395474).length < 2 ^ (prefixWord ++ tailWord_395474).sum := by decide
  have hdescent : baseEnd_395474 < baseStart_395474 := by decide
  rcases family_descends (prefixWord ++ tailWord_395474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395607 : List Nat := [1, 1, 3, 2, 3, 1, 3, 4, 4]
def baseStart_395607 : Nat := 118140960795 + 395607 * 2 ^ 59
def prefixEnd_395607 : Nat := 4983230072969 + 3 ^ 40 * 395607 * 2
def baseEnd_395607 : Nat := 45141453618519759887365

theorem tailTrace_395607 : CollatzResearch.WordTrace tailWord_395607 prefixEnd_395607 45141453618519759887365 := by
  unfold tailWord_395607
  simp only [CollatzResearch.WordTrace]
  refine ⟨14428972677790878141641075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9619315118527252094427383 14428972677790878141641075)
  ·
    refine ⟨21643459016686317212461613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14428972677790878141641075 21643459016686317212461613)
    ·
      refine ⟨8116297131257368954673105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21643459016686317212461613 8116297131257368954673105)
      ·
        refine ⟨6087222848443026716004829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8116297131257368954673105 6087222848443026716004829)
        ·
          refine ⟨2282708568166135018501811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6087222848443026716004829 2282708568166135018501811)
          ·
            refine ⟨3424062852249202527752717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2282708568166135018501811 3424062852249202527752717)
            ·
              refine ⟨1284023569593450947907269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3424062852249202527752717 1284023569593450947907269)
              ·
                refine ⟨240754419298772052732613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1284023569593450947907269 240754419298772052732613)
                ·
                  refine ⟨45141453618519759887365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 240754419298772052732613 45141453618519759887365)
                  ·
                    rfl

theorem cell22_395607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4, 4].length) (baseStart_395607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_395607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_395607 prefixEnd_395607 := by exact prefixLift 395607
  have htrace : WordTrace (prefixWord ++ tailWord_395607) baseStart_395607 baseEnd_395607 := by
    simpa [prefixWord, tailWord_395607, baseEnd_395607] using wordTrace_append hprefix tailTrace_395607
  have hstable : (prefixWord ++ tailWord_395607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395607).length < 2 ^ (prefixWord ++ tailWord_395607).sum := by decide
  have hdescent : baseEnd_395607 < baseStart_395607 := by decide
  rcases family_descends (prefixWord ++ tailWord_395607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395620 : List Nat := [2, 3, 1, 1, 3, 1, 2, 2, 1, 6]
def baseStart_395620 : Nat := 118140960795 + 395620 * 2 ^ 59
def prefixEnd_395620 : Nat := 4983230072969 + 3 ^ 40 * 395620 * 2
def baseEnd_395620 : Nat := 135428811021231579087055

theorem tailTrace_395620 : CollatzResearch.WordTrace tailWord_395620 prefixEnd_395620 135428811021231579087055 := by
  unfold tailWord_395620
  simp only [CollatzResearch.WordTrace]
  refine ⟨7214723413371890680932157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9619631217829187574576209 7214723413371890680932157)
  ·
    refine ⟨2705521280014459005349559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7214723413371890680932157 2705521280014459005349559)
    ·
      refine ⟨4058281920021688508024339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2705521280014459005349559 4058281920021688508024339)
      ·
        refine ⟨6087422880032532762036509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4058281920021688508024339 6087422880032532762036509)
        ·
          refine ⟨2282783580012199785763691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6087422880032532762036509 2282783580012199785763691)
          ·
            refine ⟨3424175370018299678645537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2282783580012199785763691 3424175370018299678645537)
            ·
              refine ⟨2568131527513724758984153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3424175370018299678645537 2568131527513724758984153)
              ·
                refine ⟨1926098645635293569238115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2568131527513724758984153 1926098645635293569238115)
                ·
                  refine ⟨2889147968452940353857173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1926098645635293569238115 2889147968452940353857173)
                  ·
                    refine ⟨135428811021231579087055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2889147968452940353857173 135428811021231579087055)
                    ·
                      rfl

theorem cell22_395620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_395620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_395620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_395620 prefixEnd_395620 := by exact prefixLift 395620
  have htrace : WordTrace (prefixWord ++ tailWord_395620) baseStart_395620 baseEnd_395620 := by
    simpa [prefixWord, tailWord_395620, baseEnd_395620] using wordTrace_append hprefix tailTrace_395620
  have hstable : (prefixWord ++ tailWord_395620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395620).length < 2 ^ (prefixWord ++ tailWord_395620).sum := by decide
  have hdescent : baseEnd_395620 < baseStart_395620 := by decide
  rcases family_descends (prefixWord ++ tailWord_395620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395637 : List Nat := [1, 3, 4, 1, 2, 2, 1, 1, 1, 6]
def baseStart_395637 : Nat := 118140960795 + 395637 * 2 ^ 59
def prefixEnd_395637 : Nat := 4983230072969 + 3 ^ 40 * 395637 * 2
def baseEnd_395637 : Nat := 135434630468649201412003

theorem tailTrace_395637 : CollatzResearch.WordTrace tailWord_395637 prefixEnd_395637 135434630468649201412003 := by
  unfold tailWord_395637
  simp only [CollatzResearch.WordTrace]
  refine ⟨14430066867682193265233165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9620044578454795510155443 14430066867682193265233165)
  ·
    refine ⟨5411275075380822474462437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14430066867682193265233165 5411275075380822474462437)
    ·
      refine ⟨1014614076633904213961707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5411275075380822474462437 1014614076633904213961707)
      ·
        refine ⟨1521921114950856320942561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1014614076633904213961707 1521921114950856320942561)
        ·
          refine ⟨1141440836213142240706921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1521921114950856320942561 1141440836213142240706921)
          ·
            refine ⟨856080627159856680530191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1141440836213142240706921 856080627159856680530191)
            ·
              refine ⟨1284120940739785020795287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 856080627159856680530191 1284120940739785020795287)
              ·
                refine ⟨1926181411109677531192931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1284120940739785020795287 1926181411109677531192931)
                ·
                  refine ⟨2889272116664516296789397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1926181411109677531192931 2889272116664516296789397)
                  ·
                    refine ⟨135434630468649201412003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2889272116664516296789397 135434630468649201412003)
                    ·
                      rfl

theorem cell22_395637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_395637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_395637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_395637 prefixEnd_395637 := by exact prefixLift 395637
  have htrace : WordTrace (prefixWord ++ tailWord_395637) baseStart_395637 baseEnd_395637 := by
    simpa [prefixWord, tailWord_395637, baseEnd_395637] using wordTrace_append hprefix tailTrace_395637
  have hstable : (prefixWord ++ tailWord_395637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395637).length < 2 ^ (prefixWord ++ tailWord_395637).sum := by decide
  have hdescent : baseEnd_395637 < baseStart_395637 := by decide
  rcases family_descends (prefixWord ++ tailWord_395637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395787 : List Nat := [1, 1, 1, 1, 7, 1, 3, 7]
def baseStart_395787 : Nat := 118140960795 + 395787 * 2 ^ 59
def prefixEnd_395787 : Nat := 4983230072969 + 3 ^ 40 * 395787 * 2
def baseEnd_395787 : Nat := 15053997614899867795727

theorem tailTrace_395787 : CollatzResearch.WordTrace tailWord_395787 prefixEnd_395787 15053997614899867795727 := by
  unfold tailWord_395787
  simp only [CollatzResearch.WordTrace]
  refine ⟨14435537817138768883193615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9623691878092512588795743 14435537817138768883193615)
  ·
    refine ⟨21653306725708153324790423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14435537817138768883193615 21653306725708153324790423)
    ·
      refine ⟨32479960088562229987185635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21653306725708153324790423 32479960088562229987185635)
      ·
        refine ⟨48719940132843344980778453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32479960088562229987185635 48719940132843344980778453)
        ·
          refine ⟨1141873596863515897986995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 48719940132843344980778453 1141873596863515897986995)
          ·
            refine ⟨1712810395295273846980493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1141873596863515897986995 1712810395295273846980493)
            ·
              refine ⟨642303898235727692617685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1712810395295273846980493 642303898235727692617685)
              ·
                refine ⟨15053997614899867795727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 642303898235727692617685 15053997614899867795727)
                ·
                  rfl

theorem cell22_395787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 7].length) (baseStart_395787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_395787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_395787 prefixEnd_395787 := by exact prefixLift 395787
  have htrace : WordTrace (prefixWord ++ tailWord_395787) baseStart_395787 baseEnd_395787 := by
    simpa [prefixWord, tailWord_395787, baseEnd_395787] using wordTrace_append hprefix tailTrace_395787
  have hstable : (prefixWord ++ tailWord_395787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395787).length < 2 ^ (prefixWord ++ tailWord_395787).sum := by decide
  have hdescent : baseEnd_395787 < baseStart_395787 := by decide
  rcases family_descends (prefixWord ++ tailWord_395787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395804 : List Nat := [2, 2, 3, 1, 2, 3, 3, 6]
def baseStart_395804 : Nat := 118140960795 + 395804 * 2 ^ 59
def prefixEnd_395804 : Nat := 4983230072969 + 3 ^ 40 * 395804 * 2
def baseEnd_395804 : Nat := 15054644220168492498499

theorem tailTrace_395804 : CollatzResearch.WordTrace tailWord_395804 prefixEnd_395804 15054644220168492498499 := by
  unfold tailWord_395804
  simp only [CollatzResearch.WordTrace]
  refine ⟨7218078929038590393281233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9624105238718120524374977 7218078929038590393281233)
  ·
    refine ⟨5413559196778942794960925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7218078929038590393281233 5413559196778942794960925)
    ·
      refine ⟨2030084698792103548110347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5413559196778942794960925 2030084698792103548110347)
      ·
        refine ⟨3045127048188155322165521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2030084698792103548110347 3045127048188155322165521)
        ·
          refine ⟨2283845286141116491624141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3045127048188155322165521 2283845286141116491624141)
          ·
            refine ⟨856441982302918684359053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2283845286141116491624141 856441982302918684359053)
            ·
              refine ⟨321165743363594506634645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 856441982302918684359053 321165743363594506634645)
              ·
                refine ⟨15054644220168492498499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 321165743363594506634645 15054644220168492498499)
                ·
                  rfl

theorem cell22_395804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 6].length) (baseStart_395804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_395804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_395804 prefixEnd_395804 := by exact prefixLift 395804
  have htrace : WordTrace (prefixWord ++ tailWord_395804) baseStart_395804 baseEnd_395804 := by
    simpa [prefixWord, tailWord_395804, baseEnd_395804] using wordTrace_append hprefix tailTrace_395804
  have hstable : (prefixWord ++ tailWord_395804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395804).length < 2 ^ (prefixWord ++ tailWord_395804).sum := by decide
  have hdescent : baseEnd_395804 < baseStart_395804 := by decide
  rcases family_descends (prefixWord ++ tailWord_395804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395832 : List Nat := [2, 1, 2, 1, 4, 1, 3, 1, 7]
def baseStart_395832 : Nat := 118140960795 + 395832 * 2 ^ 59
def prefixEnd_395832 : Nat := 4983230072969 + 3 ^ 40 * 395832 * 2
def baseEnd_395832 : Nat := 45167127651244564262135

theorem tailTrace_395832 : CollatzResearch.WordTrace tailWord_395832 prefixEnd_395832 45167127651244564262135 := by
  unfold tailWord_395832
  simp only [CollatzResearch.WordTrace]
  refine ⟨7218589550987870784290875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9624786067983827712387833 7218589550987870784290875)
  ·
    refine ⟨10827884326481806176436313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7218589550987870784290875 10827884326481806176436313)
    ·
      refine ⟨8120913244861354632327235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10827884326481806176436313 8120913244861354632327235)
      ·
        refine ⟨12181369867292031948490853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8120913244861354632327235 12181369867292031948490853)
        ·
          refine ⟨2284006850117255990342035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12181369867292031948490853 2284006850117255990342035)
          ·
            refine ⟨3426010275175883985513053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2284006850117255990342035 3426010275175883985513053)
            ·
              refine ⟨1284753853190956494567395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3426010275175883985513053 1284753853190956494567395)
              ·
                refine ⟨1927130779786434741851093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1284753853190956494567395 1927130779786434741851093)
                ·
                  refine ⟨45167127651244564262135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1927130779786434741851093 45167127651244564262135)
                  ·
                    rfl

theorem cell22_395832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 7].length) (baseStart_395832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_395832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_395832 prefixEnd_395832 := by exact prefixLift 395832
  have htrace : WordTrace (prefixWord ++ tailWord_395832) baseStart_395832 baseEnd_395832 := by
    simpa [prefixWord, tailWord_395832, baseEnd_395832] using wordTrace_append hprefix tailTrace_395832
  have hstable : (prefixWord ++ tailWord_395832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395832).length < 2 ^ (prefixWord ++ tailWord_395832).sum := by decide
  have hdescent : baseEnd_395832 < baseStart_395832 := by decide
  rcases family_descends (prefixWord ++ tailWord_395832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395836 : List Nat := [2, 2, 2, 2, 3, 2, 2, 1, 3, 3]
def baseStart_395836 : Nat := 118140960795 + 395836 * 2 ^ 59
def prefixEnd_395836 : Nat := 4983230072969 + 3 ^ 40 * 395836 * 2
def baseEnd_395836 : Nat := 135502752235479015686393

theorem tailTrace_395836 : CollatzResearch.WordTrace tailWord_395836 prefixEnd_395836 135502752235479015686393 := by
  unfold tailWord_395836
  simp only [CollatzResearch.WordTrace]
  refine ⟨7218662496980625125863681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9624883329307500167818241 7218662496980625125863681)
  ·
    refine ⟨5413996872735468844397761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7218662496980625125863681 5413996872735468844397761)
    ·
      refine ⟨4060497654551601633298321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5413996872735468844397761 4060497654551601633298321)
      ·
        refine ⟨3045373240913701224973741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4060497654551601633298321 3045373240913701224973741)
        ·
          refine ⟨1142014965342637959365153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3045373240913701224973741 1142014965342637959365153)
          ·
            refine ⟨856511224006978469523865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1142014965342637959365153 856511224006978469523865)
            ·
              refine ⟨642383418005233852142899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 856511224006978469523865 642383418005233852142899)
              ·
                refine ⟨963575127007850778214349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 642383418005233852142899 963575127007850778214349)
                ·
                  refine ⟨361340672627944041830381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 963575127007850778214349 361340672627944041830381)
                  ·
                    refine ⟨135502752235479015686393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 361340672627944041830381 135502752235479015686393)
                    ·
                      rfl

theorem cell22_395836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_395836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_395836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_395836 prefixEnd_395836 := by exact prefixLift 395836
  have htrace : WordTrace (prefixWord ++ tailWord_395836) baseStart_395836 baseEnd_395836 := by
    simpa [prefixWord, tailWord_395836, baseEnd_395836] using wordTrace_append hprefix tailTrace_395836
  have hstable : (prefixWord ++ tailWord_395836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395836).length < 2 ^ (prefixWord ++ tailWord_395836).sum := by decide
  have hdescent : baseEnd_395836 < baseStart_395836 := by decide
  rcases family_descends (prefixWord ++ tailWord_395836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395907 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 3, 6]
def baseStart_395907 : Nat := 118140960795 + 395907 * 2 ^ 59
def prefixEnd_395907 : Nat := 4983230072969 + 3 ^ 40 * 395907 * 2
def baseEnd_395907 : Nat := 135527056986458497161175

theorem tailTrace_395907 : CollatzResearch.WordTrace tailWord_395907 prefixEnd_395907 135527056986458497161175 := by
  unfold tailWord_395907
  simp only [CollatzResearch.WordTrace]
  refine ⟨14439914576704029377561975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9626609717802686251707983 14439914576704029377561975)
  ·
    refine ⟨21659871865056044066342963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14439914576704029377561975 21659871865056044066342963)
    ·
      refine ⟨32489807797584066099514445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21659871865056044066342963 32489807797584066099514445)
      ·
        refine ⟨12183677924094024787317917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32489807797584066099514445 12183677924094024787317917)
        ·
          refine ⟨4568879221535259295244219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12183677924094024787317917 4568879221535259295244219)
          ·
            refine ⟨6853318832302888942866329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4568879221535259295244219 6853318832302888942866329)
            ·
              refine ⟨5139989124227166707149747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6853318832302888942866329 5139989124227166707149747)
              ·
                refine ⟨7709983686340750060724621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5139989124227166707149747 7709983686340750060724621)
                ·
                  refine ⟨2891243882377781272771733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7709983686340750060724621 2891243882377781272771733)
                  ·
                    refine ⟨135527056986458497161175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2891243882377781272771733 135527056986458497161175)
                    ·
                      rfl

theorem cell22_395907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 6].length) (baseStart_395907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_395907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_395907 prefixEnd_395907 := by exact prefixLift 395907
  have htrace : WordTrace (prefixWord ++ tailWord_395907) baseStart_395907 baseEnd_395907 := by
    simpa [prefixWord, tailWord_395907, baseEnd_395907] using wordTrace_append hprefix tailTrace_395907
  have hstable : (prefixWord ++ tailWord_395907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395907).length < 2 ^ (prefixWord ++ tailWord_395907).sum := by decide
  have hdescent : baseEnd_395907 < baseStart_395907 := by decide
  rcases family_descends (prefixWord ++ tailWord_395907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395930 : List Nat := [3, 1, 1, 6, 1, 1, 3, 1, 1, 4]
def baseStart_395930 : Nat := 118140960795 + 395930 * 2 ^ 59
def prefixEnd_395930 : Nat := 4983230072969 + 3 ^ 40 * 395930 * 2
def baseEnd_395930 : Nat := 135534930356494103836105

theorem tailTrace_395930 : CollatzResearch.WordTrace tailWord_395930 prefixEnd_395930 135534930356494103836105 := by
  unfold tailWord_395930
  simp only [CollatzResearch.WordTrace]
  refine ⟨3610188363905176076412311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9627168970413802870432829 3610188363905176076412311)
  ·
    refine ⟨5415282545857764114618467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3610188363905176076412311 5415282545857764114618467)
    ·
      refine ⟨8122923818786646171927701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5415282545857764114618467 8122923818786646171927701)
      ·
        refine ⟨380762054005624039309111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8122923818786646171927701 380762054005624039309111)
        ·
          refine ⟨571143081008436058963667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380762054005624039309111 571143081008436058963667)
          ·
            refine ⟨856714621512654088445501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571143081008436058963667 856714621512654088445501)
            ·
              refine ⟨321267983067245283167063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 856714621512654088445501 321267983067245283167063)
              ·
                refine ⟨481901974600867924750595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321267983067245283167063 481901974600867924750595)
                ·
                  refine ⟨722852961901301887125893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 481901974600867924750595 722852961901301887125893)
                  ·
                    refine ⟨135534930356494103836105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 722852961901301887125893 135534930356494103836105)
                    ·
                      rfl

theorem cell22_395930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 1, 4].length) (baseStart_395930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_395930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_395930 prefixEnd_395930 := by exact prefixLift 395930
  have htrace : WordTrace (prefixWord ++ tailWord_395930) baseStart_395930 baseEnd_395930 := by
    simpa [prefixWord, tailWord_395930, baseEnd_395930] using wordTrace_append hprefix tailTrace_395930
  have hstable : (prefixWord ++ tailWord_395930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395930).length < 2 ^ (prefixWord ++ tailWord_395930).sum := by decide
  have hdescent : baseEnd_395930 < baseStart_395930 := by decide
  rcases family_descends (prefixWord ++ tailWord_395930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395999 : List Nat := [1, 1, 2, 3, 2, 3, 1, 2, 2, 5]
def baseStart_395999 : Nat := 118140960795 + 395999 * 2 ^ 59
def prefixEnd_395999 : Nat := 4983230072969 + 3 ^ 40 * 395999 * 2
def baseEnd_395999 : Nat := 135558550466600923860893

theorem tailTrace_395999 : CollatzResearch.WordTrace tailWord_395999 prefixEnd_395999 135558550466600923860893 := by
  unfold tailWord_395999
  simp only [CollatzResearch.WordTrace]
  refine ⟨14443270092370729089911051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9628846728247152726607367 14443270092370729089911051)
  ·
    refine ⟨21664905138556093634866577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14443270092370729089911051 21664905138556093634866577)
    ·
      refine ⟨16248678853917070226149933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21664905138556093634866577 16248678853917070226149933)
      ·
        refine ⟨6093254570218901334806225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16248678853917070226149933 6093254570218901334806225)
        ·
          refine ⟨4569940927664176001104669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6093254570218901334806225 4569940927664176001104669)
          ·
            refine ⟨1713727847874066000414251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4569940927664176001104669 1713727847874066000414251)
            ·
              refine ⟨2570591771811099000621377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1713727847874066000414251 2570591771811099000621377)
              ·
                refine ⟨1927943828858324250466033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2570591771811099000621377 1927943828858324250466033)
                ·
                  refine ⟨1445957871643743187849525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1927943828858324250466033 1445957871643743187849525)
                  ·
                    refine ⟨135558550466600923860893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1445957871643743187849525 135558550466600923860893)
                    ·
                      rfl

theorem cell22_395999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 5].length) (baseStart_395999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_395999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_395999 prefixEnd_395999 := by exact prefixLift 395999
  have htrace : WordTrace (prefixWord ++ tailWord_395999) baseStart_395999 baseEnd_395999 := by
    simpa [prefixWord, tailWord_395999, baseEnd_395999] using wordTrace_append hprefix tailTrace_395999
  have hstable : (prefixWord ++ tailWord_395999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395999).length < 2 ^ (prefixWord ++ tailWord_395999).sum := by decide
  have hdescent : baseEnd_395999 < baseStart_395999 := by decide
  rcases family_descends (prefixWord ++ tailWord_395999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396001 : List Nat := [1, 2, 3, 1, 4, 1, 3, 2, 5]
def baseStart_396001 : Nat := 118140960795 + 396001 * 2 ^ 59
def prefixEnd_396001 : Nat := 4983230072969 + 3 ^ 40 * 396001 * 2
def baseEnd_396001 : Nat := 45186411702491195103629

theorem tailTrace_396001 : CollatzResearch.WordTrace tailWord_396001 prefixEnd_396001 45186411702491195103629 := by
  unfold tailWord_396001
  simp only [CollatzResearch.WordTrace]
  refine ⟨14443343038363483431483857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9628895358908988954322571 14443343038363483431483857)
  ·
    refine ⟨10832507278772612573612893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14443343038363483431483857 10832507278772612573612893)
    ·
      refine ⟨4062190229539729715104835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10832507278772612573612893 4062190229539729715104835)
      ·
        refine ⟨6093285344309594572657253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4062190229539729715104835 6093285344309594572657253)
        ·
          refine ⟨1142491002058048982373235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6093285344309594572657253 1142491002058048982373235)
          ·
            refine ⟨1713736503087073473559853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1142491002058048982373235 1713736503087073473559853)
            ·
              refine ⟨642651188657652552584945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1713736503087073473559853 642651188657652552584945)
              ·
                refine ⟨481988391493239414438709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 642651188657652552584945 481988391493239414438709)
                ·
                  refine ⟨45186411702491195103629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 481988391493239414438709 45186411702491195103629)
                  ·
                    rfl

theorem cell22_396001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 5].length) (baseStart_396001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_396001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_396001 prefixEnd_396001 := by exact prefixLift 396001
  have htrace : WordTrace (prefixWord ++ tailWord_396001) baseStart_396001 baseEnd_396001 := by
    simpa [prefixWord, tailWord_396001, baseEnd_396001] using wordTrace_append hprefix tailTrace_396001
  have hstable : (prefixWord ++ tailWord_396001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396001).length < 2 ^ (prefixWord ++ tailWord_396001).sum := by decide
  have hdescent : baseEnd_396001 < baseStart_396001 := by decide
  rcases family_descends (prefixWord ++ tailWord_396001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396018 : List Nat := [3, 2, 1, 3, 1, 3, 3, 1, 5]
def baseStart_396018 : Nat := 118140960795 + 396018 * 2 ^ 59
def prefixEnd_396018 : Nat := 4983230072969 + 3 ^ 40 * 396018 * 2
def baseEnd_396018 : Nat := 45188351518297069211945

theorem tailTrace_396018 : CollatzResearch.WordTrace tailWord_396018 prefixEnd_396018 45188351518297069211945 := by
  unfold tailWord_396018
  simp only [CollatzResearch.WordTrace]
  refine ⟨3610990769825473833713177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9629308719534596889901805 3610990769825473833713177)
  ·
    refine ⟨2708243077369105375284883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3610990769825473833713177 2708243077369105375284883)
    ·
      refine ⟨4062364616053658062927325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2708243077369105375284883 4062364616053658062927325)
      ·
        refine ⟨1523386731020121773597747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4062364616053658062927325 1523386731020121773597747)
        ·
          refine ⟨2285080096530182660396621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1523386731020121773597747 2285080096530182660396621)
          ·
            refine ⟨856905036198818497648733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2285080096530182660396621 856905036198818497648733)
            ·
              refine ⟨321339388574556936618275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 856905036198818497648733 321339388574556936618275)
              ·
                refine ⟨482009082861835404927413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321339388574556936618275 482009082861835404927413)
                ·
                  refine ⟨45188351518297069211945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 482009082861835404927413 45188351518297069211945)
                  ·
                    rfl

theorem cell22_396018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_396018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_396018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_396018 prefixEnd_396018 := by exact prefixLift 396018
  have htrace : WordTrace (prefixWord ++ tailWord_396018) baseStart_396018 baseEnd_396018 := by
    simpa [prefixWord, tailWord_396018, baseEnd_396018] using wordTrace_append hprefix tailTrace_396018
  have hstable : (prefixWord ++ tailWord_396018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396018).length < 2 ^ (prefixWord ++ tailWord_396018).sum := by decide
  have hdescent : baseEnd_396018 < baseStart_396018 := by decide
  rcases family_descends (prefixWord ++ tailWord_396018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396029 : List Nat := [1, 4, 1, 1, 1, 1, 3, 4, 6]
def baseStart_396029 : Nat := 118140960795 + 396029 * 2 ^ 59
def prefixEnd_396029 : Nat := 4983230072969 + 3 ^ 40 * 396029 * 2
def baseEnd_396029 : Nat := 45189606693230281870267

theorem tailTrace_396029 : CollatzResearch.WordTrace tailWord_396029 prefixEnd_396029 45189606693230281870267 := by
  unfold tailWord_396029
  simp only [CollatzResearch.WordTrace]
  refine ⟨14444364282262044213503141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9629576188174696142335427 14444364282262044213503141)
  ·
    refine ⟨2708318302924133290031839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14444364282262044213503141 2708318302924133290031839)
    ·
      refine ⟨4062477454386199935047759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2708318302924133290031839 4062477454386199935047759)
      ·
        refine ⟨6093716181579299902571639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4062477454386199935047759 6093716181579299902571639)
        ·
          refine ⟨9140574272368949853857459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6093716181579299902571639 9140574272368949853857459)
          ·
            refine ⟨13710861408553424780786189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9140574272368949853857459 13710861408553424780786189)
            ·
              refine ⟨5141573028207534292794821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13710861408553424780786189 5141573028207534292794821)
              ·
                refine ⟨964044942788912679899029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5141573028207534292794821 964044942788912679899029)
                ·
                  refine ⟨45189606693230281870267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 964044942788912679899029 45189606693230281870267)
                  ·
                    rfl

theorem cell22_396029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_396029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_396029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_396029 prefixEnd_396029 := by exact prefixLift 396029
  have htrace : WordTrace (prefixWord ++ tailWord_396029) baseStart_396029 baseEnd_396029 := by
    simpa [prefixWord, tailWord_396029, baseEnd_396029] using wordTrace_append hprefix tailTrace_396029
  have hstable : (prefixWord ++ tailWord_396029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396029).length < 2 ^ (prefixWord ++ tailWord_396029).sum := by decide
  have hdescent : baseEnd_396029 < baseStart_396029 := by decide
  rcases family_descends (prefixWord ++ tailWord_396029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396044 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 3, 5]
def baseStart_396044 : Nat := 118140960795 + 396044 * 2 ^ 59
def prefixEnd_396044 : Nat := 4983230072969 + 3 ^ 40 * 396044 * 2
def baseEnd_396044 : Nat := 135573954886235806485755

theorem tailTrace_396044 : CollatzResearch.WordTrace tailWord_396044 prefixEnd_396044 135573954886235806485755 := by
  unfold tailWord_396044
  simp only [CollatzResearch.WordTrace]
  refine ⟨7222455688603850887649593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9629940918138467850199457 7222455688603850887649593)
  ·
    refine ⟨5416841766452888165737195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7222455688603850887649593 5416841766452888165737195)
    ·
      refine ⟨8125262649679332248605793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5416841766452888165737195 8125262649679332248605793)
      ·
        refine ⟨6093946987259499186454345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8125262649679332248605793 6093946987259499186454345)
        ·
          refine ⟨4570460240444624389840759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6093946987259499186454345 4570460240444624389840759)
          ·
            refine ⟨6855690360666936584761139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4570460240444624389840759 6855690360666936584761139)
            ·
              refine ⟨10283535541000404877141709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6855690360666936584761139 10283535541000404877141709)
              ·
                refine ⟨3856325827875151828928141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10283535541000404877141709 3856325827875151828928141)
                ·
                  refine ⟨1446122185453181935848053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3856325827875151828928141 1446122185453181935848053)
                  ·
                    refine ⟨135573954886235806485755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1446122185453181935848053 135573954886235806485755)
                    ·
                      rfl

theorem cell22_396044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_396044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_396044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_396044 prefixEnd_396044 := by exact prefixLift 396044
  have htrace : WordTrace (prefixWord ++ tailWord_396044) baseStart_396044 baseEnd_396044 := by
    simpa [prefixWord, tailWord_396044, baseEnd_396044] using wordTrace_append hprefix tailTrace_396044
  have hstable : (prefixWord ++ tailWord_396044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396044).length < 2 ^ (prefixWord ++ tailWord_396044).sum := by decide
  have hdescent : baseEnd_396044 < baseStart_396044 := by decide
  rcases family_descends (prefixWord ++ tailWord_396044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396106 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 7, 3]
def baseStart_396106 : Nat := 118140960795 + 396106 * 2 ^ 59
def prefixEnd_396106 : Nat := 4983230072969 + 3 ^ 40 * 396106 * 2
def baseEnd_396106 : Nat := 135595178753288311435565

theorem tailTrace_396106 : CollatzResearch.WordTrace tailWord_396106 prefixEnd_396106 135595178753288311435565 := by
  unfold tailWord_396106
  simp only [CollatzResearch.WordTrace]
  refine ⟨3611793175745771591014043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9631448468655390909370781 3611793175745771591014043)
  ·
    refine ⟨5417689763618657386521065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3611793175745771591014043 5417689763618657386521065)
    ·
      refine ⟨4063267322713993039890799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5417689763618657386521065 4063267322713993039890799)
      ·
        refine ⟨6094900984070989559836199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4063267322713993039890799 6094900984070989559836199)
        ·
          refine ⟨9142351476106484339754299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6094900984070989559836199 9142351476106484339754299)
          ·
            refine ⟨13713527214159726509631449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9142351476106484339754299 13713527214159726509631449)
            ·
              refine ⟨10285145410619794882223587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13713527214159726509631449 10285145410619794882223587)
              ·
                refine ⟨15427718115929692323335381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10285145410619794882223587 15427718115929692323335381)
                ·
                  refine ⟨361587143342102163828173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15427718115929692323335381 361587143342102163828173)
                  ·
                    refine ⟨135595178753288311435565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 361587143342102163828173 135595178753288311435565)
                    ·
                      rfl

theorem cell22_396106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_396106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_396106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_396106 prefixEnd_396106 := by exact prefixLift 396106
  have htrace : WordTrace (prefixWord ++ tailWord_396106) baseStart_396106 baseEnd_396106 := by
    simpa [prefixWord, tailWord_396106, baseEnd_396106] using wordTrace_append hprefix tailTrace_396106
  have hstable : (prefixWord ++ tailWord_396106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396106).length < 2 ^ (prefixWord ++ tailWord_396106).sum := by decide
  have hdescent : baseEnd_396106 < baseStart_396106 := by decide
  rcases family_descends (prefixWord ++ tailWord_396106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396170 : List Nat := [3, 1, 2, 4, 1, 3, 1, 2, 5]
def baseStart_396170 : Nat := 118140960795 + 396170 * 2 ^ 59
def prefixEnd_396170 : Nat := 4983230072969 + 3 ^ 40 * 396170 * 2
def baseEnd_396170 : Nat := 45205695753737825945123

theorem tailTrace_396170 : CollatzResearch.WordTrace tailWord_396170 prefixEnd_396170 45205695753737825945123 := by
  unfold tailWord_396170
  simp only [CollatzResearch.WordTrace]
  refine ⟨3612376743687806323596491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9633004649834150196257309 3612376743687806323596491)
  ·
    refine ⟨5418565115531709485394737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3612376743687806323596491 5418565115531709485394737)
    ·
      refine ⟨4063923836648782114046053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5418565115531709485394737 4063923836648782114046053)
      ·
        refine ⟨761985719371646646383635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4063923836648782114046053 761985719371646646383635)
        ·
          refine ⟨1142978579057469969575453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 761985719371646646383635 1142978579057469969575453)
          ·
            refine ⟨428616967146551238590795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1142978579057469969575453 428616967146551238590795)
            ·
              refine ⟨642925450719826857886193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428616967146551238590795 642925450719826857886193)
              ·
                refine ⟨482194088039870143414645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 642925450719826857886193 482194088039870143414645)
                ·
                  refine ⟨45205695753737825945123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 482194088039870143414645 45205695753737825945123)
                  ·
                    rfl

theorem cell22_396170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 5].length) (baseStart_396170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_396170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_396170 prefixEnd_396170 := by exact prefixLift 396170
  have htrace : WordTrace (prefixWord ++ tailWord_396170) baseStart_396170 baseEnd_396170 := by
    simpa [prefixWord, tailWord_396170, baseEnd_396170] using wordTrace_append hprefix tailTrace_396170
  have hstable : (prefixWord ++ tailWord_396170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396170).length < 2 ^ (prefixWord ++ tailWord_396170).sum := by decide
  have hdescent : baseEnd_396170 < baseStart_396170 := by decide
  rcases family_descends (prefixWord ++ tailWord_396170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396181 : List Nat := [1, 3, 2, 1, 1, 4, 1, 3, 6]
def baseStart_396181 : Nat := 118140960795 + 396181 * 2 ^ 59
def prefixEnd_396181 : Nat := 4983230072969 + 3 ^ 40 * 396181 * 2
def baseEnd_396181 : Nat := 45206950928671038603445

theorem tailTrace_396181 : CollatzResearch.WordTrace tailWord_396181 prefixEnd_396181 45206950928671038603445 := by
  unfold tailWord_396181
  simp only [CollatzResearch.WordTrace]
  refine ⟨14449908177711374173036397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9633272118474249448690931 14449908177711374173036397)
  ·
    refine ⟨5418715566641765314888649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14449908177711374173036397 5418715566641765314888649)
    ·
      refine ⟨4064036674981323986166487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5418715566641765314888649 4064036674981323986166487)
      ·
        refine ⟨6096055012471985979249731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4064036674981323986166487 6096055012471985979249731)
        ·
          refine ⟨9144082518707978968874597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6096055012471985979249731 9144082518707978968874597)
          ·
            refine ⟨1714515472257746056663987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9144082518707978968874597 1714515472257746056663987)
            ·
              refine ⟨2571773208386619084995981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1714515472257746056663987 2571773208386619084995981)
              ·
                refine ⟨964414953144982156873493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2571773208386619084995981 964414953144982156873493)
                ·
                  refine ⟨45206950928671038603445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 964414953144982156873493 45206950928671038603445)
                  ·
                    rfl

theorem cell22_396181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 6].length) (baseStart_396181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_396181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_396181 prefixEnd_396181 := by exact prefixLift 396181
  have htrace : WordTrace (prefixWord ++ tailWord_396181) baseStart_396181 baseEnd_396181 := by
    simpa [prefixWord, tailWord_396181, baseEnd_396181] using wordTrace_append hprefix tailTrace_396181
  have hstable : (prefixWord ++ tailWord_396181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396181).length < 2 ^ (prefixWord ++ tailWord_396181).sum := by decide
  have hdescent : baseEnd_396181 < baseStart_396181 := by decide
  rcases family_descends (prefixWord ++ tailWord_396181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396213 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 6, 3]
def baseStart_396213 : Nat := 118140960795 + 396213 * 2 ^ 59
def prefixEnd_396213 : Nat := 4983230072969 + 3 ^ 40 * 396213 * 2
def baseEnd_396213 : Nat := 135631807039975699010237

theorem tailTrace_396213 : CollatzResearch.WordTrace tailWord_396213 prefixEnd_396213 135631807039975699010237 := by
  unfold tailWord_396213
  simp only [CollatzResearch.WordTrace]
  refine ⟨14451075313595443638201293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9634050209063629092134195 14451075313595443638201293)
  ·
    refine ⟨5419153242598291364325485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14451075313595443638201293 5419153242598291364325485)
    ·
      refine ⟨2032182465974359261622057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5419153242598291364325485 2032182465974359261622057)
      ·
        refine ⟨1524136849480769446216543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2032182465974359261622057 1524136849480769446216543)
        ·
          refine ⟨2286205274221154169324815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1524136849480769446216543 2286205274221154169324815)
          ·
            refine ⟨3429307911331731253987223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2286205274221154169324815 3429307911331731253987223)
            ·
              refine ⟨5143961866997596880980835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3429307911331731253987223 5143961866997596880980835)
              ·
                refine ⟨7715942800496395321471253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5143961866997596880980835 7715942800496395321471253)
                ·
                  refine ⟨361684818773268530693965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7715942800496395321471253 361684818773268530693965)
                  ·
                    refine ⟨135631807039975699010237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 361684818773268530693965 135631807039975699010237)
                    ·
                      rfl

theorem cell22_396213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_396213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_396213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_396213 prefixEnd_396213 := by exact prefixLift 396213
  have htrace : WordTrace (prefixWord ++ tailWord_396213) baseStart_396213 baseEnd_396213 := by
    simpa [prefixWord, tailWord_396213, baseEnd_396213] using wordTrace_append hprefix tailTrace_396213
  have hstable : (prefixWord ++ tailWord_396213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396213).length < 2 ^ (prefixWord ++ tailWord_396213).sum := by decide
  have hdescent : baseEnd_396213 < baseStart_396213 := by decide
  rcases family_descends (prefixWord ++ tailWord_396213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396232 : List Nat := [2, 1, 3, 1, 5, 1, 3, 2, 4]
def baseStart_396232 : Nat := 118140960795 + 396232 * 2 ^ 59
def prefixEnd_396232 : Nat := 4983230072969 + 3 ^ 40 * 396232 * 2
def baseEnd_396232 : Nat := 45212770376088660928393

theorem tailTrace_396232 : CollatzResearch.WordTrace tailWord_396232 prefixEnd_396232 45212770376088660928393 := by
  unfold tailWord_396232
  simp only [CollatzResearch.WordTrace]
  refine ⟨7225884150263304941571475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9634512200351073255428633 7225884150263304941571475)
  ·
    refine ⟨10838826225394957412357213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7225884150263304941571475 10838826225394957412357213)
    ·
      refine ⟨4064559834523109029633955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10838826225394957412357213 4064559834523109029633955)
      ·
        refine ⟨6096839751784663544450933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4064559834523109029633955 6096839751784663544450933)
        ·
          refine ⟨571578726729812207292275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6096839751784663544450933 571578726729812207292275)
          ·
            refine ⟨857368090094718310938413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571578726729812207292275 857368090094718310938413)
            ·
              refine ⟨321513033785519366601905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 857368090094718310938413 321513033785519366601905)
              ·
                refine ⟨241134775339139524951429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321513033785519366601905 241134775339139524951429)
                ·
                  refine ⟨45212770376088660928393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 241134775339139524951429 45212770376088660928393)
                  ·
                    rfl

theorem cell22_396232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2, 4].length) (baseStart_396232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_396232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_396232 prefixEnd_396232 := by exact prefixLift 396232
  have htrace : WordTrace (prefixWord ++ tailWord_396232) baseStart_396232 baseEnd_396232 := by
    simpa [prefixWord, tailWord_396232, baseEnd_396232] using wordTrace_append hprefix tailTrace_396232
  have hstable : (prefixWord ++ tailWord_396232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396232).length < 2 ^ (prefixWord ++ tailWord_396232).sum := by decide
  have hdescent : baseEnd_396232 < baseStart_396232 := by decide
  rcases family_descends (prefixWord ++ tailWord_396232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396350 : List Nat := [4, 2, 1, 3, 1, 1, 1, 3, 6]
def baseStart_396350 : Nat := 118140960795 + 396350 * 2 ^ 59
def prefixEnd_396350 : Nat := 4983230072969 + 3 ^ 40 * 396350 * 2
def baseEnd_396350 : Nat := 45226234979917669444939

theorem tailTrace_396350 : CollatzResearch.WordTrace tailWord_396350 prefixEnd_396350 45226234979917669444939 := by
  unfold tailWord_396350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1807009014262389504492313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9637381409399410690625669 1807009014262389504492313)
  ·
    refine ⟨1355256760696792128369235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1807009014262389504492313 1355256760696792128369235)
    ·
      refine ⟨2032885141045188192553853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1355256760696792128369235 2032885141045188192553853)
      ·
        refine ⟨762331927891945572207695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2032885141045188192553853 762331927891945572207695)
        ·
          refine ⟨1143497891837918358311543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 762331927891945572207695 1143497891837918358311543)
          ·
            refine ⟨1715246837756877537467315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1143497891837918358311543 1715246837756877537467315)
            ·
              refine ⟨2572870256635316306200973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1715246837756877537467315 2572870256635316306200973)
              ·
                refine ⟨964826346238243614825365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2572870256635316306200973 964826346238243614825365)
                ·
                  refine ⟨45226234979917669444939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 964826346238243614825365 45226234979917669444939)
                  ·
                    rfl

theorem cell22_396350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_396350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_396350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_396350 prefixEnd_396350 := by exact prefixLift 396350
  have htrace : WordTrace (prefixWord ++ tailWord_396350) baseStart_396350 baseEnd_396350 := by
    simpa [prefixWord, tailWord_396350, baseEnd_396350] using wordTrace_append hprefix tailTrace_396350
  have hstable : (prefixWord ++ tailWord_396350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396350).length < 2 ^ (prefixWord ++ tailWord_396350).sum := by decide
  have hdescent : baseEnd_396350 < baseStart_396350 := by decide
  rcases family_descends (prefixWord ++ tailWord_396350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396380 : List Nat := [2, 2, 4, 1, 1, 1, 2, 3, 2, 4]
def baseStart_396380 : Nat := 118140960795 + 396380 * 2 ^ 59
def prefixEnd_396380 : Nat := 4983230072969 + 3 ^ 40 * 396380 * 2
def baseEnd_396380 : Nat := 135688974552842930084725

theorem tailTrace_396380 : CollatzResearch.WordTrace tailWord_396380 prefixEnd_396380 135688974552842930084725 := by
  unfold tailWord_396380
  simp only [CollatzResearch.WordTrace]
  refine ⟨7228583151995215579765297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9638110869326954106353729 7228583151995215579765297)
  ·
    refine ⟨5421437363996411684823973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7228583151995215579765297 5421437363996411684823973)
    ·
      refine ⟨1016519505749327190904495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5421437363996411684823973 1016519505749327190904495)
      ·
        refine ⟨1524779258623990786356743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1016519505749327190904495 1524779258623990786356743)
        ·
          refine ⟨2287168887935986179535115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1524779258623990786356743 2287168887935986179535115)
          ·
            refine ⟨3430753331903979269302673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2287168887935986179535115 3430753331903979269302673)
            ·
              refine ⟨2573064998927984451977005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3430753331903979269302673 2573064998927984451977005)
              ·
                refine ⟨964899374597994169491377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2573064998927984451977005 964899374597994169491377)
                ·
                  refine ⟨723674530948495627118533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 964899374597994169491377 723674530948495627118533)
                  ·
                    refine ⟨135688974552842930084725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 723674530948495627118533 135688974552842930084725)
                    ·
                      rfl

theorem cell22_396380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_396380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_396380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_396380 prefixEnd_396380 := by exact prefixLift 396380
  have htrace : WordTrace (prefixWord ++ tailWord_396380) baseStart_396380 baseEnd_396380 := by
    simpa [prefixWord, tailWord_396380, baseEnd_396380] using wordTrace_append hprefix tailTrace_396380
  have hstable : (prefixWord ++ tailWord_396380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396380).length < 2 ^ (prefixWord ++ tailWord_396380).sum := by decide
  have hdescent : baseEnd_396380 < baseStart_396380 := by decide
  rcases family_descends (prefixWord ++ tailWord_396380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396461 : List Nat := [1, 5, 2, 1, 3, 1, 1, 4, 1, 3]
def baseStart_396461 : Nat := 118140960795 + 396461 * 2 ^ 59
def prefixEnd_396461 : Nat := 4983230072969 + 3 ^ 40 * 396461 * 2
def baseEnd_396461 : Nat := 135716702508185718809477

theorem tailTrace_396461 : CollatzResearch.WordTrace tailWord_396461 prefixEnd_396461 135716702508185718809477 := by
  unfold tailWord_396461
  simp only [CollatzResearch.WordTrace]
  refine ⟨14460120616696981993229237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9640080411131321328819491 14460120616696981993229237)
  ·
    refine ⟨1355636307815342061865241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14460120616696981993229237 1355636307815342061865241)
    ·
      refine ⟨1016727230861506546398931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1355636307815342061865241 1016727230861506546398931)
      ·
        refine ⟨1525090846292259819598397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1016727230861506546398931 1525090846292259819598397)
        ·
          refine ⟨571909067359597432349399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1525090846292259819598397 571909067359597432349399)
          ·
            refine ⟨857863601039396148524099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571909067359597432349399 857863601039396148524099)
            ·
              refine ⟨1286795401559094222786149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 857863601039396148524099 1286795401559094222786149)
              ·
                refine ⟨241274137792330166772403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1286795401559094222786149 241274137792330166772403)
                ·
                  refine ⟨361911206688495250158605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241274137792330166772403 361911206688495250158605)
                  ·
                    refine ⟨135716702508185718809477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 361911206688495250158605 135716702508185718809477)
                    ·
                      rfl

theorem cell22_396461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_396461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_396461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_396461 prefixEnd_396461 := by exact prefixLift 396461
  have htrace : WordTrace (prefixWord ++ tailWord_396461) baseStart_396461 baseEnd_396461 := by
    simpa [prefixWord, tailWord_396461, baseEnd_396461] using wordTrace_append hprefix tailTrace_396461
  have hstable : (prefixWord ++ tailWord_396461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396461).length < 2 ^ (prefixWord ++ tailWord_396461).sum := by decide
  have hdescent : baseEnd_396461 < baseStart_396461 := by decide
  rcases family_descends (prefixWord ++ tailWord_396461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396547 : List Nat := [1, 1, 1, 3, 2, 6, 2, 6]
def baseStart_396547 : Nat := 118140960795 + 396547 * 2 ^ 59
def prefixEnd_396547 : Nat := 4983230072969 + 3 ^ 40 * 396547 * 2
def baseEnd_396547 : Nat := 15082904673967795684357

theorem tailTrace_396547 : CollatzResearch.WordTrace tailWord_396547 prefixEnd_396547 15082904673967795684357 := by
  unfold tailWord_396547
  simp only [CollatzResearch.WordTrace]
  refine ⟨14463257294385418680859895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9642171529590279120573263 14463257294385418680859895)
  ·
    refine ⟨21694885941578128021289843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14463257294385418680859895 21694885941578128021289843)
    ·
      refine ⟨32542328912367192031934765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21694885941578128021289843 32542328912367192031934765)
      ·
        refine ⟨12203373342137697011975537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32542328912367192031934765 12203373342137697011975537)
        ·
          refine ⟨9152530006603272758981653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12203373342137697011975537 9152530006603272758981653)
          ·
            refine ⟨429024844059528410577265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9152530006603272758981653 429024844059528410577265)
            ·
              refine ⟨321768633044646307932949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 429024844059528410577265 321768633044646307932949)
              ·
                refine ⟨15082904673967795684357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 321768633044646307932949 15082904673967795684357)
                ·
                  rfl

theorem cell22_396547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 6].length) (baseStart_396547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_396547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_396547 prefixEnd_396547 := by exact prefixLift 396547
  have htrace : WordTrace (prefixWord ++ tailWord_396547) baseStart_396547 baseEnd_396547 := by
    simpa [prefixWord, tailWord_396547, baseEnd_396547] using wordTrace_append hprefix tailTrace_396547
  have hstable : (prefixWord ++ tailWord_396547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396547).length < 2 ^ (prefixWord ++ tailWord_396547).sum := by decide
  have hdescent : baseEnd_396547 < baseStart_396547 := by decide
  rcases family_descends (prefixWord ++ tailWord_396547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396579 : List Nat := [1, 1, 1, 4, 2, 5, 1, 1, 3, 3]
def baseStart_396579 : Nat := 118140960795 + 396579 * 2 ^ 59
def prefixEnd_396579 : Nat := 4983230072969 + 3 ^ 40 * 396579 * 2
def baseEnd_396579 : Nat := 135757096319672744359115

theorem tailTrace_396579 : CollatzResearch.WordTrace tailWord_396579 prefixEnd_396579 135757096319672744359115 := by
  unfold tailWord_396579
  simp only [CollatzResearch.WordTrace]
  refine ⟨14464424430269488146024791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9642949620179658764016527 14464424430269488146024791)
  ·
    refine ⟨21696636645404232219037187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14464424430269488146024791 21696636645404232219037187)
    ·
      refine ⟨32544954968106348328555781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21696636645404232219037187 32544954968106348328555781)
      ·
        refine ⟨6102179056519940311604209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32544954968106348328555781 6102179056519940311604209)
        ·
          refine ⟨4576634292389955233703157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6102179056519940311604209 4576634292389955233703157)
          ·
            refine ⟨429059464911558303159671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4576634292389955233703157 429059464911558303159671)
            ·
              refine ⟨643589197367337454739507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429059464911558303159671 643589197367337454739507)
              ·
                refine ⟨965383796051006182109261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 643589197367337454739507 965383796051006182109261)
                ·
                  refine ⟨362018923519127318290973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 965383796051006182109261 362018923519127318290973)
                  ·
                    refine ⟨135757096319672744359115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 362018923519127318290973 135757096319672744359115)
                    ·
                      rfl

theorem cell22_396579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3, 3].length) (baseStart_396579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_396579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_396579 prefixEnd_396579 := by exact prefixLift 396579
  have htrace : WordTrace (prefixWord ++ tailWord_396579) baseStart_396579 baseEnd_396579 := by
    simpa [prefixWord, tailWord_396579, baseEnd_396579] using wordTrace_append hprefix tailTrace_396579
  have hstable : (prefixWord ++ tailWord_396579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396579).length < 2 ^ (prefixWord ++ tailWord_396579).sum := by decide
  have hdescent : baseEnd_396579 < baseStart_396579 := by decide
  rcases family_descends (prefixWord ++ tailWord_396579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396652 : List Nat := [2, 2, 1, 1, 5, 1, 1, 3, 1, 5]
def baseStart_396652 : Nat := 118140960795 + 396652 * 2 ^ 59
def prefixEnd_396652 : Nat := 4983230072969 + 3 ^ 40 * 396652 * 2
def baseEnd_396652 : Nat := 135782085711524887283891

theorem tailTrace_396652 : CollatzResearch.WordTrace tailWord_396652 prefixEnd_396652 135782085711524887283891 := by
  unfold tailWord_396652
  simp only [CollatzResearch.WordTrace]
  refine ⟨7233543479502510806716105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9644724639336681075621473 7233543479502510806716105)
  ·
    refine ⟨5425157609626883105037079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7233543479502510806716105 5425157609626883105037079)
    ·
      refine ⟨8137736414440324657555619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5425157609626883105037079 8137736414440324657555619)
      ·
        refine ⟨12206604621660486986333429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8137736414440324657555619 12206604621660486986333429)
        ·
          refine ⟨1144369183280670654968759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12206604621660486986333429 1144369183280670654968759)
          ·
            refine ⟨1716553774921005982453139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1144369183280670654968759 1716553774921005982453139)
            ·
              refine ⟨2574830662381508973679709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1716553774921005982453139 2574830662381508973679709)
              ·
                refine ⟨965561498393065865129891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2574830662381508973679709 965561498393065865129891)
                ·
                  refine ⟨1448342247589598797694837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 965561498393065865129891 1448342247589598797694837)
                  ·
                    refine ⟨135782085711524887283891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1448342247589598797694837 135782085711524887283891)
                    ·
                      rfl

theorem cell22_396652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_396652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_396652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_396652 prefixEnd_396652 := by exact prefixLift 396652
  have htrace : WordTrace (prefixWord ++ tailWord_396652) baseStart_396652 baseEnd_396652 := by
    simpa [prefixWord, tailWord_396652, baseEnd_396652] using wordTrace_append hprefix tailTrace_396652
  have hstable : (prefixWord ++ tailWord_396652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396652).length < 2 ^ (prefixWord ++ tailWord_396652).sum := by decide
  have hdescent : baseEnd_396652 < baseStart_396652 := by decide
  rcases family_descends (prefixWord ++ tailWord_396652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396665 : List Nat := [1, 2, 1, 3, 2, 1, 2, 10]
def baseStart_396665 : Nat := 118140960795 + 396665 * 2 ^ 59
def prefixEnd_396665 : Nat := 4983230072969 + 3 ^ 40 * 396665 * 2
def baseEnd_396665 : Nat := 15087392875244131856539

theorem tailTrace_396665 : CollatzResearch.WordTrace tailWord_396665 prefixEnd_396665 15087392875244131856539 := by
  unfold tailWord_396665
  simp only [CollatzResearch.WordTrace]
  refine ⟨14467561107957924833655449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9645040738638616555770299 14467561107957924833655449)
  ·
    refine ⟨10850670830968443625241587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14467561107957924833655449 10850670830968443625241587)
    ·
      refine ⟨16276006246452665437862381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10850670830968443625241587 16276006246452665437862381)
      ·
        refine ⟨6103502342419749539198393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16276006246452665437862381 6103502342419749539198393)
        ·
          refine ⟨4577626756814812154398795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6103502342419749539198393 4577626756814812154398795)
          ·
            refine ⟨6866440135222218231598193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4577626756814812154398795 6866440135222218231598193)
            ·
              refine ⟨5149830101416663673698645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6866440135222218231598193 5149830101416663673698645)
              ·
                refine ⟨15087392875244131856539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5149830101416663673698645 15087392875244131856539)
                ·
                  rfl

theorem cell22_396665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 10].length) (baseStart_396665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_396665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_396665 prefixEnd_396665 := by exact prefixLift 396665
  have htrace : WordTrace (prefixWord ++ tailWord_396665) baseStart_396665 baseEnd_396665 := by
    simpa [prefixWord, tailWord_396665, baseEnd_396665] using wordTrace_append hprefix tailTrace_396665
  have hstable : (prefixWord ++ tailWord_396665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396665).length < 2 ^ (prefixWord ++ tailWord_396665).sum := by decide
  have hdescent : baseEnd_396665 < baseStart_396665 := by decide
  rcases family_descends (prefixWord ++ tailWord_396665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396673 : List Nat := [1, 2, 4, 3, 2, 2, 2, 1, 1, 4]
def baseStart_396673 : Nat := 118140960795 + 396673 * 2 ^ 59
def prefixEnd_396673 : Nat := 4983230072969 + 3 ^ 40 * 396673 * 2
def baseEnd_396673 : Nat := 135789274440687832508827

theorem tailTrace_396673 : CollatzResearch.WordTrace tailWord_396673 prefixEnd_396673 135789274440687832508827 := by
  unfold tailWord_396673
  simp only [CollatzResearch.WordTrace]
  refine ⟨14467852891928942199946673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9645235261285961466631115 14467852891928942199946673)
  ·
    refine ⟨10850889668946706649960005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14467852891928942199946673 10850889668946706649960005)
    ·
      refine ⟨2034541812927507496867501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10850889668946706649960005 2034541812927507496867501)
      ·
        refine ⟨762953179847815311325313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2034541812927507496867501 762953179847815311325313)
        ·
          refine ⟨572214884885861483493985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 762953179847815311325313 572214884885861483493985)
          ·
            refine ⟨429161163664396112620489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 572214884885861483493985 429161163664396112620489)
            ·
              refine ⟨321870872748297084465367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 429161163664396112620489 321870872748297084465367)
              ·
                refine ⟨482806309122445626698051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321870872748297084465367 482806309122445626698051)
                ·
                  refine ⟨724209463683668440047077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 482806309122445626698051 724209463683668440047077)
                  ·
                    refine ⟨135789274440687832508827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 724209463683668440047077 135789274440687832508827)
                    ·
                      rfl

theorem cell22_396673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_396673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_396673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_396673 prefixEnd_396673 := by exact prefixLift 396673
  have htrace : WordTrace (prefixWord ++ tailWord_396673) baseStart_396673 baseEnd_396673 := by
    simpa [prefixWord, tailWord_396673, baseEnd_396673] using wordTrace_append hprefix tailTrace_396673
  have hstable : (prefixWord ++ tailWord_396673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396673).length < 2 ^ (prefixWord ++ tailWord_396673).sum := by decide
  have hdescent : baseEnd_396673 < baseStart_396673 := by decide
  rcases family_descends (prefixWord ++ tailWord_396673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396686 : List Nat := [4, 1, 1, 4, 2, 1, 1, 1, 4, 3]
def baseStart_396686 : Nat := 118140960795 + 396686 * 2 ^ 59
def prefixEnd_396686 : Nat := 4983230072969 + 3 ^ 40 * 396686 * 2
def baseEnd_396686 : Nat := 135793724606360131933787

theorem tailTrace_396686 : CollatzResearch.WordTrace tailWord_396686 prefixEnd_396686 135793724606360131933787 := by
  unfold tailWord_396686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1808540880110230677521239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9645551360587896946779941 1808540880110230677521239)
  ·
    refine ⟨2712811320165346016281859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1808540880110230677521239 2712811320165346016281859)
    ·
      refine ⟨4069216980248019024422789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2712811320165346016281859 4069216980248019024422789)
      ·
        refine ⟨762978183796503567079273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4069216980248019024422789 762978183796503567079273)
        ·
          refine ⟨572233637847377675309455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 762978183796503567079273 572233637847377675309455)
          ·
            refine ⟨858350456771066512964183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572233637847377675309455 858350456771066512964183)
            ·
              refine ⟨1287525685156599769446275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 858350456771066512964183 1287525685156599769446275)
              ·
                refine ⟨1931288527734899654169413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1287525685156599769446275 1931288527734899654169413)
                ·
                  refine ⟨362116598950293685156765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1931288527734899654169413 362116598950293685156765)
                  ·
                    refine ⟨135793724606360131933787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 362116598950293685156765 135793724606360131933787)
                    ·
                      rfl

theorem cell22_396686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_396686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_396686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_396686 prefixEnd_396686 := by exact prefixLift 396686
  have htrace : WordTrace (prefixWord ++ tailWord_396686) baseStart_396686 baseEnd_396686 := by
    simpa [prefixWord, tailWord_396686, baseEnd_396686] using wordTrace_append hprefix tailTrace_396686
  have hstable : (prefixWord ++ tailWord_396686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396686).length < 2 ^ (prefixWord ++ tailWord_396686).sum := by decide
  have hdescent : baseEnd_396686 < baseStart_396686 := by decide
  rcases family_descends (prefixWord ++ tailWord_396686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396761 : List Nat := [1, 2, 1, 2, 4, 4, 2, 1, 5]
def baseStart_396761 : Nat := 118140960795 + 396761 * 2 ^ 59
def prefixEnd_396761 : Nat := 4983230072969 + 3 ^ 40 * 396761 * 2
def baseEnd_396761 : Nat := 45273132879694978769519

theorem tailTrace_396761 : CollatzResearch.WordTrace tailWord_396761 prefixEnd_396761 45273132879694978769519 := by
  unfold tailWord_396761
  simp only [CollatzResearch.WordTrace]
  refine ⟨14471062515610133229150137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9647375010406755486100091 14471062515610133229150137)
  ·
    refine ⟨10853296886707599921862603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14471062515610133229150137 10853296886707599921862603)
    ·
      refine ⟨16279945330061399882793905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10853296886707599921862603 16279945330061399882793905)
      ·
        refine ⟨12209958997546049912095429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16279945330061399882793905 12209958997546049912095429)
        ·
          refine ⟨2289367312039884358517893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12209958997546049912095429 2289367312039884358517893)
          ·
            refine ⟨429256371007478317222105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2289367312039884358517893 429256371007478317222105)
            ·
              refine ⟨321942278255608737916579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 429256371007478317222105 321942278255608737916579)
              ·
                refine ⟨482913417383413106874869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321942278255608737916579 482913417383413106874869)
                ·
                  refine ⟨45273132879694978769519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 482913417383413106874869 45273132879694978769519)
                  ·
                    rfl

theorem cell22_396761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 5].length) (baseStart_396761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_396761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_396761 prefixEnd_396761 := by exact prefixLift 396761
  have htrace : WordTrace (prefixWord ++ tailWord_396761) baseStart_396761 baseEnd_396761 := by
    simpa [prefixWord, tailWord_396761, baseEnd_396761] using wordTrace_append hprefix tailTrace_396761
  have hstable : (prefixWord ++ tailWord_396761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396761).length < 2 ^ (prefixWord ++ tailWord_396761).sum := by decide
  have hdescent : baseEnd_396761 < baseStart_396761 := by decide
  rcases family_descends (prefixWord ++ tailWord_396761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396772 : List Nat := [2, 3, 1, 1, 1, 1, 1, 6, 6]
def baseStart_396772 : Nat := 118140960795 + 396772 * 2 ^ 59
def prefixEnd_396772 : Nat := 4983230072969 + 3 ^ 40 * 396772 * 2
def baseEnd_396772 : Nat := 45274388054628191427841

theorem tailTrace_396772 : CollatzResearch.WordTrace tailWord_396772 prefixEnd_396772 45274388054628191427841 := by
  unfold tailWord_396772
  simp only [CollatzResearch.WordTrace]
  refine ⟨7235731859285141053900285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9647642479046854738533713 7235731859285141053900285)
  ·
    refine ⟨2713399447231927895212607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7235731859285141053900285 2713399447231927895212607)
    ·
      refine ⟨4070099170847891842818911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2713399447231927895212607 4070099170847891842818911)
      ·
        refine ⟨6105148756271837764228367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4070099170847891842818911 6105148756271837764228367)
        ·
          refine ⟨9157723134407756646342551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6105148756271837764228367 9157723134407756646342551)
          ·
            refine ⟨13736584701611634969513827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9157723134407756646342551 13736584701611634969513827)
            ·
              refine ⟨20604877052417452454270741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13736584701611634969513827 20604877052417452454270741)
              ·
                refine ⟨965853611832068083793941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20604877052417452454270741 965853611832068083793941)
                ·
                  refine ⟨45274388054628191427841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 965853611832068083793941 45274388054628191427841)
                  ·
                    rfl

theorem cell22_396772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_396772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_396772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_396772 prefixEnd_396772 := by exact prefixLift 396772
  have htrace : WordTrace (prefixWord ++ tailWord_396772) baseStart_396772 baseEnd_396772 := by
    simpa [prefixWord, tailWord_396772, baseEnd_396772] using wordTrace_append hprefix tailTrace_396772
  have hstable : (prefixWord ++ tailWord_396772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396772).length < 2 ^ (prefixWord ++ tailWord_396772).sum := by decide
  have hdescent : baseEnd_396772 < baseStart_396772 := by decide
  rcases family_descends (prefixWord ++ tailWord_396772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396821 : List Nat := [1, 3, 2, 1, 3, 2, 2, 3, 2, 3]
def baseStart_396821 : Nat := 118140960795 + 396821 * 2 ^ 59
def prefixEnd_396821 : Nat := 4983230072969 + 3 ^ 40 * 396821 * 2
def baseEnd_396821 : Nat := 135839937865264779808373

theorem tailTrace_396821 : CollatzResearch.WordTrace tailWord_396821 prefixEnd_396821 135839937865264779808373 := by
  unfold tailWord_396821
  simp only [CollatzResearch.WordTrace]
  refine ⟨14473250895392763476334317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9648833930261842317556211 14473250895392763476334317)
  ·
    refine ⟨5427469085772286303625369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14473250895392763476334317 5427469085772286303625369)
    ·
      refine ⟨4070601814329214727719027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5427469085772286303625369 4070601814329214727719027)
      ·
        refine ⟨6105902721493822091578541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4070601814329214727719027 6105902721493822091578541)
        ·
          refine ⟨2289713520560183284341953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6105902721493822091578541 2289713520560183284341953)
          ·
            refine ⟨1717285140420137463256465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2289713520560183284341953 1717285140420137463256465)
            ·
              refine ⟨1287963855315103097442349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1717285140420137463256465 1287963855315103097442349)
              ·
                refine ⟨482986445743163661540881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1287963855315103097442349 482986445743163661540881)
                ·
                  refine ⟨362239834307372746155661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 482986445743163661540881 362239834307372746155661)
                  ·
                    refine ⟨135839937865264779808373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 362239834307372746155661 135839937865264779808373)
                    ·
                      rfl

theorem cell22_396821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_396821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_396821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_396821 prefixEnd_396821 := by exact prefixLift 396821
  have htrace : WordTrace (prefixWord ++ tailWord_396821) baseStart_396821 baseEnd_396821 := by
    simpa [prefixWord, tailWord_396821, baseEnd_396821] using wordTrace_append hprefix tailTrace_396821
  have hstable : (prefixWord ++ tailWord_396821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396821).length < 2 ^ (prefixWord ++ tailWord_396821).sum := by decide
  have hdescent : baseEnd_396821 < baseStart_396821 := by decide
  rcases family_descends (prefixWord ++ tailWord_396821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396849 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 7, 3]
def baseStart_396849 : Nat := 118140960795 + 396849 * 2 ^ 59
def prefixEnd_396849 : Nat := 4983230072969 + 3 ^ 40 * 396849 * 2
def baseEnd_396849 : Nat := 135849522837482040108287

theorem tailTrace_396849 : CollatzResearch.WordTrace tailWord_396849 prefixEnd_396849 135849522837482040108287 := by
  unfold tailWord_396849
  simp only [CollatzResearch.WordTrace]
  refine ⟨14474272139291324258353601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9649514759527549505569067 14474272139291324258353601)
  ·
    refine ⟨10855704104468493193765201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14474272139291324258353601 10855704104468493193765201)
    ·
      refine ⟨8141778078351369895323901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10855704104468493193765201 8141778078351369895323901)
      ·
        refine ⟨3053166779381763710746463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8141778078351369895323901 3053166779381763710746463)
        ·
          refine ⟨4579750169072645566119695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3053166779381763710746463 4579750169072645566119695)
          ·
            refine ⟨6869625253608968349179543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4579750169072645566119695 6869625253608968349179543)
            ·
              refine ⟨10304437880413452523769315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6869625253608968349179543 10304437880413452523769315)
              ·
                refine ⟨15456656820620178785653973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10304437880413452523769315 15456656820620178785653973)
                ·
                  refine ⟨362265394233285440288765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15456656820620178785653973 362265394233285440288765)
                  ·
                    refine ⟨135849522837482040108287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 362265394233285440288765 135849522837482040108287)
                    ·
                      rfl

theorem cell22_396849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7, 3].length) (baseStart_396849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_396849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_396849 prefixEnd_396849 := by exact prefixLift 396849
  have htrace : WordTrace (prefixWord ++ tailWord_396849) baseStart_396849 baseEnd_396849 := by
    simpa [prefixWord, tailWord_396849, baseEnd_396849] using wordTrace_append hprefix tailTrace_396849
  have hstable : (prefixWord ++ tailWord_396849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396849).length < 2 ^ (prefixWord ++ tailWord_396849).sum := by decide
  have hdescent : baseEnd_396849 < baseStart_396849 := by decide
  rcases family_descends (prefixWord ++ tailWord_396849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396900 : List Nat := [2, 3, 1, 1, 2, 5, 1, 3, 1, 3]
def baseStart_396900 : Nat := 118140960795 + 396900 * 2 ^ 59
def prefixEnd_396900 : Nat := 4983230072969 + 3 ^ 40 * 396900 * 2
def baseEnd_396900 : Nat := 135866981179734907083131

theorem tailTrace_396900 : CollatzResearch.WordTrace tailWord_396900 prefixEnd_396900 135866981179734907083131 := by
  unfold tailWord_396900
  simp only [CollatzResearch.WordTrace]
  refine ⟨7238066131053279984230077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9650754841404373312306769 7238066131053279984230077)
  ·
    refine ⟨2714274799144979994086279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7238066131053279984230077 2714274799144979994086279)
    ·
      refine ⟨4071412198717469991129419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2714274799144979994086279 4071412198717469991129419)
      ·
        refine ⟨6107118298076204986694129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4071412198717469991129419 6107118298076204986694129)
        ·
          refine ⟨4580338723557153740020597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6107118298076204986694129 4580338723557153740020597)
          ·
            refine ⟨429406755333483163126931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4580338723557153740020597 429406755333483163126931)
            ·
              refine ⟨644110133000224744690397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429406755333483163126931 644110133000224744690397)
              ·
                refine ⟨241541299875084279258899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 644110133000224744690397 241541299875084279258899)
                ·
                  refine ⟨362311949812626418888349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241541299875084279258899 362311949812626418888349)
                  ·
                    refine ⟨135866981179734907083131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 362311949812626418888349 135866981179734907083131)
                    ·
                      rfl

theorem cell22_396900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_396900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_396900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_396900 prefixEnd_396900 := by exact prefixLift 396900
  have htrace : WordTrace (prefixWord ++ tailWord_396900) baseStart_396900 baseEnd_396900 := by
    simpa [prefixWord, tailWord_396900, baseEnd_396900] using wordTrace_append hprefix tailTrace_396900
  have hstable : (prefixWord ++ tailWord_396900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396900).length < 2 ^ (prefixWord ++ tailWord_396900).sum := by decide
  have hdescent : baseEnd_396900 < baseStart_396900 := by decide
  rcases family_descends (prefixWord ++ tailWord_396900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396917 : List Nat := [1, 3, 4, 2, 1, 2, 3, 2, 1, 3]
def baseStart_396917 : Nat := 118140960795 + 396917 * 2 ^ 59
def prefixEnd_396917 : Nat := 4983230072969 + 3 ^ 40 * 396917 * 2
def baseEnd_396917 : Nat := 135872800627152529408079

theorem tailTrace_396917 : CollatzResearch.WordTrace tailWord_396917 prefixEnd_396917 135872800627152529408079 := by
  unfold tailWord_396917
  simp only [CollatzResearch.WordTrace]
  refine ⟨14476752303044971871829005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9651168202029981247886003 14476752303044971871829005)
  ·
    refine ⟨5428782113641864451935877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14476752303044971871829005 5428782113641864451935877)
    ·
      refine ⟨1017896646307849584737977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5428782113641864451935877 1017896646307849584737977)
      ·
        refine ⟨763422484730887188553483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1017896646307849584737977 763422484730887188553483)
        ·
          refine ⟨1145133727096330782830225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 763422484730887188553483 1145133727096330782830225)
          ·
            refine ⟨858850295322248087122669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1145133727096330782830225 858850295322248087122669)
            ·
              refine ⟨322068860745843032671001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 858850295322248087122669 322068860745843032671001)
              ·
                refine ⟨241551645559382274503251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322068860745843032671001 241551645559382274503251)
                ·
                  refine ⟨362327468339073411754877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241551645559382274503251 362327468339073411754877)
                  ·
                    refine ⟨135872800627152529408079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 362327468339073411754877 135872800627152529408079)
                    ·
                      rfl

theorem cell22_396917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_396917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_396917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_396917 prefixEnd_396917 := by exact prefixLift 396917
  have htrace : WordTrace (prefixWord ++ tailWord_396917) baseStart_396917 baseEnd_396917 := by
    simpa [prefixWord, tailWord_396917, baseEnd_396917] using wordTrace_append hprefix tailTrace_396917
  have hstable : (prefixWord ++ tailWord_396917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396917).length < 2 ^ (prefixWord ++ tailWord_396917).sum := by decide
  have hdescent : baseEnd_396917 < baseStart_396917 := by decide
  rcases family_descends (prefixWord ++ tailWord_396917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396939 : List Nat := [1, 1, 1, 1, 4, 1, 4, 3, 1, 5]
def baseStart_396939 : Nat := 118140960795 + 396939 * 2 ^ 59
def prefixEnd_396939 : Nat := 4983230072969 + 3 ^ 40 * 396939 * 2
def baseEnd_396939 : Nat := 135880331676751805358011

theorem tailTrace_396939 : CollatzResearch.WordTrace tailWord_396939 prefixEnd_396939 135880331676751805358011 := by
  unfold tailWord_396939
  simp only [CollatzResearch.WordTrace]
  refine ⟨14477554708965269629129871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9651703139310179752753247 14477554708965269629129871)
  ·
    refine ⟨21716332063447904443694807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14477554708965269629129871 21716332063447904443694807)
    ·
      refine ⟨32574498095171856665542211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21716332063447904443694807 32574498095171856665542211)
      ·
        refine ⟨48861747142757784998313317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32574498095171856665542211 48861747142757784998313317)
        ·
          refine ⟨9161577589267084687183747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48861747142757784998313317 9161577589267084687183747)
          ·
            refine ⟨13742366383900627030775621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9161577589267084687183747 13742366383900627030775621)
            ·
              refine ⟨2576693696981367568270429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13742366383900627030775621 2576693696981367568270429)
              ·
                refine ⟨966260136368012838101411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2576693696981367568270429 966260136368012838101411)
                ·
                  refine ⟨1449390204552019257152117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 966260136368012838101411 1449390204552019257152117)
                  ·
                    refine ⟨135880331676751805358011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1449390204552019257152117 135880331676751805358011)
                    ·
                      rfl

theorem cell22_396939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 5].length) (baseStart_396939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_396939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_396939 prefixEnd_396939 := by exact prefixLift 396939
  have htrace : WordTrace (prefixWord ++ tailWord_396939) baseStart_396939 baseEnd_396939 := by
    simpa [prefixWord, tailWord_396939, baseEnd_396939] using wordTrace_append hprefix tailTrace_396939
  have hstable : (prefixWord ++ tailWord_396939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396939).length < 2 ^ (prefixWord ++ tailWord_396939).sum := by decide
  have hdescent : baseEnd_396939 < baseStart_396939 := by decide
  rcases family_descends (prefixWord ++ tailWord_396939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396968 : List Nat := [2, 1, 7, 1, 2, 1, 2, 2, 1, 3]
def baseStart_396968 : Nat := 118140960795 + 396968 * 2 ^ 59
def prefixEnd_396968 : Nat := 4983230072969 + 3 ^ 40 * 396968 * 2
def baseEnd_396968 : Nat := 135890258969405396382923

theorem tailTrace_396968 : CollatzResearch.WordTrace tailWord_396968 prefixEnd_396968 135890258969405396382923 := by
  unfold tailWord_396968
  simp only [CollatzResearch.WordTrace]
  refine ⟨7239306212930103790967779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9652408283906805054623705 7239306212930103790967779)
  ·
    refine ⟨10858959319395155686451669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7239306212930103790967779 10858959319395155686451669)
    ·
      refine ⟨254506859048323961401211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 10858959319395155686451669 254506859048323961401211)
      ·
        refine ⟨381760288572485942101817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254506859048323961401211 381760288572485942101817)
        ·
          refine ⟨286320216429364456576363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381760288572485942101817 286320216429364456576363)
          ·
            refine ⟨429480324644046684864545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286320216429364456576363 429480324644046684864545)
            ·
              refine ⟨322110243483035013648409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 429480324644046684864545 322110243483035013648409)
              ·
                refine ⟨241582682612276260236307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322110243483035013648409 241582682612276260236307)
                ·
                  refine ⟨362374023918414390354461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241582682612276260236307 362374023918414390354461)
                  ·
                    refine ⟨135890258969405396382923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 362374023918414390354461 135890258969405396382923)
                    ·
                      rfl

theorem cell22_396968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_396968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_396968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_396968 prefixEnd_396968 := by exact prefixLift 396968
  have htrace : WordTrace (prefixWord ++ tailWord_396968) baseStart_396968 baseEnd_396968 := by
    simpa [prefixWord, tailWord_396968, baseEnd_396968] using wordTrace_append hprefix tailTrace_396968
  have hstable : (prefixWord ++ tailWord_396968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396968).length < 2 ^ (prefixWord ++ tailWord_396968).sum := by decide
  have hdescent : baseEnd_396968 < baseStart_396968 := by decide
  rcases family_descends (prefixWord ++ tailWord_396968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396986 : List Nat := [3, 1, 1, 1, 2, 6, 1, 7]
def baseStart_396986 : Nat := 118140960795 + 396986 * 2 ^ 59
def prefixEnd_396986 : Nat := 4983230072969 + 3 ^ 40 * 396986 * 2
def baseEnd_396986 : Nat := 15099602304139927714763

theorem tailTrace_396986 : CollatzResearch.WordTrace tailWord_396986 prefixEnd_396986 15099602304139927714763 := by
  unfold tailWord_396986
  simp only [CollatzResearch.WordTrace]
  refine ⟨3619817234948749164022703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9652845959863331104060541 3619817234948749164022703)
  ·
    refine ⟨5429725852423123746034055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3619817234948749164022703 5429725852423123746034055)
    ·
      refine ⟨8144588778634685619051083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5429725852423123746034055 8144588778634685619051083)
      ·
        refine ⟨12216883167952028428576625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8144588778634685619051083 12216883167952028428576625)
        ·
          refine ⟨9162662375964021321432469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12216883167952028428576625 9162662375964021321432469)
          ·
            refine ⟨429499798873313499442147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9162662375964021321432469 429499798873313499442147)
            ·
              refine ⟨644249698309970249163221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429499798873313499442147 644249698309970249163221)
              ·
                refine ⟨15099602304139927714763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 644249698309970249163221 15099602304139927714763)
                ·
                  rfl

theorem cell22_396986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 7].length) (baseStart_396986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_396986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_396986 prefixEnd_396986 := by exact prefixLift 396986
  have htrace : WordTrace (prefixWord ++ tailWord_396986) baseStart_396986 baseEnd_396986 := by
    simpa [prefixWord, tailWord_396986, baseEnd_396986] using wordTrace_append hprefix tailTrace_396986
  have hstable : (prefixWord ++ tailWord_396986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396986).length < 2 ^ (prefixWord ++ tailWord_396986).sum := by decide
  have hdescent : baseEnd_396986 < baseStart_396986 := by decide
  rcases family_descends (prefixWord ++ tailWord_396986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396999 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 2, 6]
def baseStart_396999 : Nat := 118140960795 + 396999 * 2 ^ 59
def prefixEnd_396999 : Nat := 4983230072969 + 3 ^ 40 * 396999 * 2
def baseEnd_396999 : Nat := 135900870902931648857827

theorem tailTrace_396999 : CollatzResearch.WordTrace tailWord_396999 prefixEnd_396999 135900870902931648857827 := by
  unfold tailWord_396999
  simp only [CollatzResearch.WordTrace]
  refine ⟨14479743088747899876314051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9653162059165266584209367 14479743088747899876314051)
  ·
    refine ⟨21719614633121849814471077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14479743088747899876314051 21719614633121849814471077)
    ·
      refine ⟨4072427743710346840213327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21719614633121849814471077 4072427743710346840213327)
      ·
        refine ⟨6108641615565520260319991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4072427743710346840213327 6108641615565520260319991)
        ·
          refine ⟨9162962423348280390479987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6108641615565520260319991 9162962423348280390479987)
          ·
            refine ⟨13744443635022420585719981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9162962423348280390479987 13744443635022420585719981)
            ·
              refine ⟨5154166363133407719644993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13744443635022420585719981 5154166363133407719644993)
              ·
                refine ⟨3865624772350055789733745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5154166363133407719644993 3865624772350055789733745)
                ·
                  refine ⟨2899218579262541842300309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3865624772350055789733745 2899218579262541842300309)
                  ·
                    refine ⟨135900870902931648857827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2899218579262541842300309 135900870902931648857827)
                    ·
                      rfl

theorem cell22_396999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_396999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_396999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_396999 prefixEnd_396999 := by exact prefixLift 396999
  have htrace : WordTrace (prefixWord ++ tailWord_396999) baseStart_396999 baseEnd_396999 := by
    simpa [prefixWord, tailWord_396999, baseEnd_396999] using wordTrace_append hprefix tailTrace_396999
  have hstable : (prefixWord ++ tailWord_396999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396999).length < 2 ^ (prefixWord ++ tailWord_396999).sum := by decide
  have hdescent : baseEnd_396999 < baseStart_396999 := by decide
  rcases family_descends (prefixWord ++ tailWord_396999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397005 : List Nat := [1, 6, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_397005 : Nat := 118140960795 + 397005 * 2 ^ 59
def prefixEnd_397005 : Nat := 4983230072969 + 3 ^ 40 * 397005 * 2
def baseEnd_397005 : Nat := 135902924825549633207809

theorem tailTrace_397005 : CollatzResearch.WordTrace tailWord_397005 prefixEnd_397005 135902924825549633207809 := by
  unfold tailWord_397005
  simp only [CollatzResearch.WordTrace]
  refine ⟨14479961926726162901032469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9653307951150775267354979 14479961926726162901032469)
  ·
    refine ⟨678748215315288885985897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14479961926726162901032469 678748215315288885985897)
    ·
      refine ⟨509061161486466664489423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 678748215315288885985897 509061161486466664489423)
      ·
        refine ⟨763591742229699996734135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509061161486466664489423 763591742229699996734135)
        ·
          refine ⟨1145387613344549995101203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 763591742229699996734135 1145387613344549995101203)
          ·
            refine ⟨1718081420016824992651805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1145387613344549995101203 1718081420016824992651805)
            ·
              refine ⟨644280532506309372244427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1718081420016824992651805 644280532506309372244427)
              ·
                refine ⟨966420798759464058366641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 644280532506309372244427 966420798759464058366641)
                ·
                  refine ⟨724815599069598043774981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 966420798759464058366641 724815599069598043774981)
                  ·
                    refine ⟨135902924825549633207809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 724815599069598043774981 135902924825549633207809)
                    ·
                      rfl

theorem cell22_397005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_397005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397005 prefixEnd_397005 := by exact prefixLift 397005
  have htrace : WordTrace (prefixWord ++ tailWord_397005) baseStart_397005 baseEnd_397005 := by
    simpa [prefixWord, tailWord_397005, baseEnd_397005] using wordTrace_append hprefix tailTrace_397005
  have hstable : (prefixWord ++ tailWord_397005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397005).length < 2 ^ (prefixWord ++ tailWord_397005).sum := by decide
  have hdescent : baseEnd_397005 < baseStart_397005 := by decide
  rcases family_descends (prefixWord ++ tailWord_397005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397086 : List Nat := [4, 3, 2, 2, 2, 1, 1, 1, 3, 3]
def baseStart_397086 : Nat := 118140960795 + 397086 * 2 ^ 59
def prefixEnd_397086 : Nat := 4983230072969 + 3 ^ 40 * 397086 * 2
def baseEnd_397086 : Nat := 135930652780892421932561

theorem tailTrace_397086 : CollatzResearch.WordTrace tailWord_397086 prefixEnd_397086 135930652780892421932561 := by
  unfold tailWord_397086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1810364529929089216841389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9655277492955142489820741 1810364529929089216841389)
  ·
    refine ⟨678886698723408456315521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1810364529929089216841389 678886698723408456315521)
    ·
      refine ⟨509165024042556342236641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 678886698723408456315521 509165024042556342236641)
      ·
        refine ⟨381873768031917256677481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 509165024042556342236641 381873768031917256677481)
        ·
          refine ⟨286405326023937942508111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381873768031917256677481 286405326023937942508111)
          ·
            refine ⟨429607989035906913762167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286405326023937942508111 429607989035906913762167)
            ·
              refine ⟨644411983553860370643251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429607989035906913762167 644411983553860370643251)
              ·
                refine ⟨966617975330790555964877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 644411983553860370643251 966617975330790555964877)
                ·
                  refine ⟨362481740749046458486829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 966617975330790555964877 362481740749046458486829)
                  ·
                    refine ⟨135930652780892421932561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 362481740749046458486829 135930652780892421932561)
                    ·
                      rfl

theorem cell22_397086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_397086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397086 prefixEnd_397086 := by exact prefixLift 397086
  have htrace : WordTrace (prefixWord ++ tailWord_397086) baseStart_397086 baseEnd_397086 := by
    simpa [prefixWord, tailWord_397086, baseEnd_397086] using wordTrace_append hprefix tailTrace_397086
  have hstable : (prefixWord ++ tailWord_397086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397086).length < 2 ^ (prefixWord ++ tailWord_397086).sum := by decide
  have hdescent : baseEnd_397086 < baseStart_397086 := by decide
  rcases family_descends (prefixWord ++ tailWord_397086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397093 : List Nat := [1, 3, 1, 2, 3, 4, 1, 1, 6]
def baseStart_397093 : Nat := 118140960795 + 397093 * 2 ^ 59
def prefixEnd_397093 : Nat := 4983230072969 + 3 ^ 40 * 397093 * 2
def baseEnd_397093 : Nat := 45311016341315579002513

theorem tailTrace_397093 : CollatzResearch.WordTrace tailWord_397093 prefixEnd_397093 45311016341315579002513 := by
  unfold tailWord_397093
  simp only [CollatzResearch.WordTrace]
  refine ⟨14483171550407353930235933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9655447700271569286823955 14483171550407353930235933)
  ·
    refine ⟨5431189331402757723838475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14483171550407353930235933 5431189331402757723838475)
    ·
      refine ⟨8146783997104136585757713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5431189331402757723838475 8146783997104136585757713)
      ·
        refine ⟨6110087997828102439318285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8146783997104136585757713 6110087997828102439318285)
        ·
          refine ⟨2291282999185538414744357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6110087997828102439318285 2291282999185538414744357)
          ·
            refine ⟨429615562347288452764567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2291282999185538414744357 429615562347288452764567)
            ·
              refine ⟨644423343520932679146851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429615562347288452764567 644423343520932679146851)
              ·
                refine ⟨966635015281399018720277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 644423343520932679146851 966635015281399018720277)
                ·
                  refine ⟨45311016341315579002513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 966635015281399018720277 45311016341315579002513)
                  ·
                    rfl

theorem cell22_397093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 6].length) (baseStart_397093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397093 prefixEnd_397093 := by exact prefixLift 397093
  have htrace : WordTrace (prefixWord ++ tailWord_397093) baseStart_397093 baseEnd_397093 := by
    simpa [prefixWord, tailWord_397093, baseEnd_397093] using wordTrace_append hprefix tailTrace_397093
  have hstable : (prefixWord ++ tailWord_397093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397093).length < 2 ^ (prefixWord ++ tailWord_397093).sum := by decide
  have hdescent : baseEnd_397093 < baseStart_397093 := by decide
  rcases family_descends (prefixWord ++ tailWord_397093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397123 : List Nat := [1, 1, 1, 3, 1, 6, 2, 1, 2, 4]
def baseStart_397123 : Nat := 118140960795 + 397123 * 2 ^ 59
def prefixEnd_397123 : Nat := 4983230072969 + 3 ^ 40 * 397123 * 2
def baseEnd_397123 : Nat := 135943318637036658757447

theorem tailTrace_397123 : CollatzResearch.WordTrace tailWord_397123 prefixEnd_397123 135943318637036658757447 := by
  unfold tailWord_397123
  simp only [CollatzResearch.WordTrace]
  refine ⟨14484265740298669053828023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9656177160199112702552015 14484265740298669053828023)
  ·
    refine ⟨21726398610448003580742035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14484265740298669053828023 21726398610448003580742035)
    ·
      refine ⟨32589597915672005371113053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21726398610448003580742035 32589597915672005371113053)
      ·
        refine ⟨12221099218377002014167395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32589597915672005371113053 12221099218377002014167395)
        ·
          refine ⟨18331648827565503021251093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12221099218377002014167395 18331648827565503021251093)
          ·
            refine ⟨859296038792132954121145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18331648827565503021251093 859296038792132954121145)
            ·
              refine ⟨644472029094099715590859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 859296038792132954121145 644472029094099715590859)
              ·
                refine ⟨966708043641149573386289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 644472029094099715590859 966708043641149573386289)
                ·
                  refine ⟨725031032730862180039717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 966708043641149573386289 725031032730862180039717)
                  ·
                    refine ⟨135943318637036658757447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 725031032730862180039717 135943318637036658757447)
                    ·
                      rfl

theorem cell22_397123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 4].length) (baseStart_397123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397123 prefixEnd_397123 := by exact prefixLift 397123
  have htrace : WordTrace (prefixWord ++ tailWord_397123) baseStart_397123 baseEnd_397123 := by
    simpa [prefixWord, tailWord_397123, baseEnd_397123] using wordTrace_append hprefix tailTrace_397123
  have hstable : (prefixWord ++ tailWord_397123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397123).length < 2 ^ (prefixWord ++ tailWord_397123).sum := by decide
  have hdescent : baseEnd_397123 < baseStart_397123 := by decide
  rcases family_descends (prefixWord ++ tailWord_397123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397151 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 2, 6]
def baseStart_397151 : Nat := 118140960795 + 397151 * 2 ^ 59
def prefixEnd_397151 : Nat := 4983230072969 + 3 ^ 40 * 397151 * 2
def baseEnd_397151 : Nat := 135952903609253919057361

theorem tailTrace_397151 : CollatzResearch.WordTrace tailWord_397151 prefixEnd_397151 135952903609253919057361 := by
  unfold tailWord_397151
  simp only [CollatzResearch.WordTrace]
  refine ⟨14485286984197229835847307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9656857989464819890564871 14485286984197229835847307)
  ·
    refine ⟨21727930476295844753770961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14485286984197229835847307 21727930476295844753770961)
    ·
      refine ⟨16295947857221883565328221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21727930476295844753770961 16295947857221883565328221)
      ·
        refine ⟨6110980446458206336998083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16295947857221883565328221 6110980446458206336998083)
        ·
          refine ⟨9166470669687309505497125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6110980446458206336998083 9166470669687309505497125)
          ·
            refine ⟨1718713250566370532280711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9166470669687309505497125 1718713250566370532280711)
            ·
              refine ⟨2578069875849555798421067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1718713250566370532280711 2578069875849555798421067)
              ·
                refine ⟨3867104813774333697631601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2578069875849555798421067 3867104813774333697631601)
                ·
                  refine ⟨2900328610330750273223701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3867104813774333697631601 2900328610330750273223701)
                  ·
                    refine ⟨135952903609253919057361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2900328610330750273223701 135952903609253919057361)
                    ·
                      rfl

theorem cell22_397151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 6].length) (baseStart_397151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397151 prefixEnd_397151 := by exact prefixLift 397151
  have htrace : WordTrace (prefixWord ++ tailWord_397151) baseStart_397151 baseEnd_397151 := by
    simpa [prefixWord, tailWord_397151, baseEnd_397151] using wordTrace_append hprefix tailTrace_397151
  have hstable : (prefixWord ++ tailWord_397151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397151).length < 2 ^ (prefixWord ++ tailWord_397151).sum := by decide
  have hdescent : baseEnd_397151 < baseStart_397151 := by decide
  rcases family_descends (prefixWord ++ tailWord_397151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397153 : List Nat := [1, 2, 3, 1, 1, 1, 4, 3, 3, 3]
def baseStart_397153 : Nat := 118140960795 + 397153 * 2 ^ 59
def prefixEnd_397153 : Nat := 4983230072969 + 3 ^ 40 * 397153 * 2
def baseEnd_397153 : Nat := 135953588250126580507355

theorem tailTrace_397153 : CollatzResearch.WordTrace tailWord_397153 prefixEnd_397153 135953588250126580507355 := by
  unfold tailWord_397153
  simp only [CollatzResearch.WordTrace]
  refine ⟨14485359930189984177420113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9656906620126656118280075 14485359930189984177420113)
  ·
    refine ⟨10864019947642488133065085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14485359930189984177420113 10864019947642488133065085)
    ·
      refine ⟨4074007480365933049899407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10864019947642488133065085 4074007480365933049899407)
      ·
        refine ⟨6111011220548899574849111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4074007480365933049899407 6111011220548899574849111)
        ·
          refine ⟨9166516830823349362273667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6111011220548899574849111 9166516830823349362273667)
          ·
            refine ⟨13749775246235024043410501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9166516830823349362273667 13749775246235024043410501)
            ·
              refine ⟨2578082858669067008139469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13749775246235024043410501 2578082858669067008139469)
              ·
                refine ⟨966781072000900128052301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2578082858669067008139469 966781072000900128052301)
                ·
                  refine ⟨362542902000337548019613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 966781072000900128052301 362542902000337548019613)
                  ·
                    refine ⟨135953588250126580507355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 362542902000337548019613 135953588250126580507355)
                    ·
                      rfl

theorem cell22_397153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_397153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397153 prefixEnd_397153 := by exact prefixLift 397153
  have htrace : WordTrace (prefixWord ++ tailWord_397153) baseStart_397153 baseEnd_397153 := by
    simpa [prefixWord, tailWord_397153, baseEnd_397153] using wordTrace_append hprefix tailTrace_397153
  have hstable : (prefixWord ++ tailWord_397153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397153).length < 2 ^ (prefixWord ++ tailWord_397153).sum := by decide
  have hdescent : baseEnd_397153 < baseStart_397153 := by decide
  rcases family_descends (prefixWord ++ tailWord_397153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397155 : List Nat := [1, 1, 1, 5, 5, 1, 1, 7]
def baseStart_397155 : Nat := 118140960795 + 397155 * 2 ^ 59
def prefixEnd_397155 : Nat := 4983230072969 + 3 ^ 40 * 397155 * 2
def baseEnd_397155 : Nat := 15106030321222137995261

theorem tailTrace_397155 : CollatzResearch.WordTrace tailWord_397155 prefixEnd_397155 15106030321222137995261 := by
  unfold tailWord_397155
  simp only [CollatzResearch.WordTrace]
  refine ⟨14485432876182738518992919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9656955250788492345995279 14485432876182738518992919)
  ·
    refine ⟨21728149314274107778489379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14485432876182738518992919 21728149314274107778489379)
    ·
      refine ⟨32592223971411161667734069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21728149314274107778489379 32592223971411161667734069)
      ·
        refine ⟨3055520997319796406350069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32592223971411161667734069 3055520997319796406350069)
        ·
          refine ⟨286455093498730913095319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3055520997319796406350069 286455093498730913095319)
          ·
            refine ⟨429682640248096369642979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286455093498730913095319 429682640248096369642979)
            ·
              refine ⟨644523960372144554464469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429682640248096369642979 644523960372144554464469)
              ·
                refine ⟨15106030321222137995261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 644523960372144554464469 15106030321222137995261)
                ·
                  rfl

theorem cell22_397155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 7].length) (baseStart_397155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397155 prefixEnd_397155 := by exact prefixLift 397155
  have htrace : WordTrace (prefixWord ++ tailWord_397155) baseStart_397155 baseEnd_397155 := by
    simpa [prefixWord, tailWord_397155, baseEnd_397155] using wordTrace_append hprefix tailTrace_397155
  have hstable : (prefixWord ++ tailWord_397155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397155).length < 2 ^ (prefixWord ++ tailWord_397155).sum := by decide
  have hdescent : baseEnd_397155 < baseStart_397155 := by decide
  rcases family_descends (prefixWord ++ tailWord_397155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397174 : List Nat := [5, 1, 1, 3, 3, 1, 1, 1, 2, 4]
def baseStart_397174 : Nat := 118140960795 + 397174 * 2 ^ 59
def prefixEnd_397174 : Nat := 4983230072969 + 3 ^ 40 * 397174 * 2
def baseEnd_397174 : Nat := 135960776979289525732291

theorem tailTrace_397174 : CollatzResearch.WordTrace tailWord_397174 prefixEnd_397174 135960776979289525732291 := by
  unfold tailWord_397174
  simp only [CollatzResearch.WordTrace]
  refine ⟨905382866444619047745911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9657417242075936509289717 905382866444619047745911)
  ·
    refine ⟨1358074299666928571618867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 905382866444619047745911 1358074299666928571618867)
    ·
      refine ⟨2037111449500392857428301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1358074299666928571618867 2037111449500392857428301)
      ·
        refine ⟨763916793562647321535613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2037111449500392857428301 763916793562647321535613)
        ·
          refine ⟨286468797585992745575855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 763916793562647321535613 286468797585992745575855)
          ·
            refine ⟨429703196378989118363783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286468797585992745575855 429703196378989118363783)
            ·
              refine ⟨644554794568483677545675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429703196378989118363783 644554794568483677545675)
              ·
                refine ⟨966832191852725516318513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 644554794568483677545675 966832191852725516318513)
                ·
                  refine ⟨725124143889544137238885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 966832191852725516318513 725124143889544137238885)
                  ·
                    refine ⟨135960776979289525732291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 725124143889544137238885 135960776979289525732291)
                    ·
                      rfl

theorem cell22_397174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_397174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397174 prefixEnd_397174 := by exact prefixLift 397174
  have htrace : WordTrace (prefixWord ++ tailWord_397174) baseStart_397174 baseEnd_397174 := by
    simpa [prefixWord, tailWord_397174, baseEnd_397174] using wordTrace_append hprefix tailTrace_397174
  have hstable : (prefixWord ++ tailWord_397174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397174).length < 2 ^ (prefixWord ++ tailWord_397174).sum := by decide
  have hdescent : baseEnd_397174 < baseStart_397174 := by decide
  rcases family_descends (prefixWord ++ tailWord_397174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397181 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 3, 7]
def baseStart_397181 : Nat := 118140960795 + 397181 * 2 ^ 59
def prefixEnd_397181 : Nat := 4983230072969 + 3 ^ 40 * 397181 * 2
def baseEnd_397181 : Nat := 135963173222343840807269

theorem tailTrace_397181 : CollatzResearch.WordTrace tailWord_397181 prefixEnd_397181 135963173222343840807269 := by
  unfold tailWord_397181
  simp only [CollatzResearch.WordTrace]
  refine ⟨14486381174088544959439397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9657587449392363306292931 14486381174088544959439397)
  ·
    refine ⟨2716196470141602179894887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14486381174088544959439397 2716196470141602179894887)
    ·
      refine ⟨4074294705212403269842331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2716196470141602179894887 4074294705212403269842331)
      ·
        refine ⟨6111442057818604904763497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4074294705212403269842331 6111442057818604904763497)
        ·
          refine ⟨4583581543363953678572623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6111442057818604904763497 4583581543363953678572623)
          ·
            refine ⟨6875372315045930517858935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4583581543363953678572623 6875372315045930517858935)
            ·
              refine ⟨10313058472568895776788403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6875372315045930517858935 10313058472568895776788403)
              ·
                refine ⟨15469587708853343665182605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10313058472568895776788403 15469587708853343665182605)
                ·
                  refine ⟨5801095390820003874443477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15469587708853343665182605 5801095390820003874443477)
                  ·
                    refine ⟨135963173222343840807269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5801095390820003874443477 135963173222343840807269)
                    ·
                      rfl

theorem cell22_397181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_397181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397181 prefixEnd_397181 := by exact prefixLift 397181
  have htrace : WordTrace (prefixWord ++ tailWord_397181) baseStart_397181 baseEnd_397181 := by
    simpa [prefixWord, tailWord_397181, baseEnd_397181] using wordTrace_append hprefix tailTrace_397181
  have hstable : (prefixWord ++ tailWord_397181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397181).length < 2 ^ (prefixWord ++ tailWord_397181).sum := by decide
  have hdescent : baseEnd_397181 < baseStart_397181 := by decide
  rcases family_descends (prefixWord ++ tailWord_397181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397187 : List Nat := [1, 1, 1, 3, 4, 3, 2, 3, 1, 3]
def baseStart_397187 : Nat := 118140960795 + 397187 * 2 ^ 59
def prefixEnd_397187 : Nat := 4983230072969 + 3 ^ 40 * 397187 * 2
def baseEnd_397187 : Nat := 135965227144961825157251

theorem tailTrace_397187 : CollatzResearch.WordTrace tailWord_397187 prefixEnd_397187 135965227144961825157251 := by
  unfold tailWord_397187
  simp only [CollatzResearch.WordTrace]
  refine ⟨14486600012066807984157815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9657733341377871989438543 14486600012066807984157815)
  ·
    refine ⟨21729900018100211976236723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14486600012066807984157815 21729900018100211976236723)
    ·
      refine ⟨32594850027150317964355085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21729900018100211976236723 32594850027150317964355085)
      ·
        refine ⟨12223068760181369236633157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32594850027150317964355085 12223068760181369236633157)
        ·
          refine ⟨2291825392534006731868717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12223068760181369236633157 2291825392534006731868717)
          ·
            refine ⟨859434522200252524450769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2291825392534006731868717 859434522200252524450769)
            ·
              refine ⟨644575891650189393338077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 859434522200252524450769 644575891650189393338077)
              ·
                refine ⟨241715959368821022501779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 644575891650189393338077 241715959368821022501779)
                ·
                  refine ⟨362573939053231533752669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241715959368821022501779 362573939053231533752669)
                  ·
                    refine ⟨135965227144961825157251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 362573939053231533752669 135965227144961825157251)
                    ·
                      rfl

theorem cell22_397187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3, 1, 3].length) (baseStart_397187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397187 prefixEnd_397187 := by exact prefixLift 397187
  have htrace : WordTrace (prefixWord ++ tailWord_397187) baseStart_397187 baseEnd_397187 := by
    simpa [prefixWord, tailWord_397187, baseEnd_397187] using wordTrace_append hprefix tailTrace_397187
  have hstable : (prefixWord ++ tailWord_397187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397187).length < 2 ^ (prefixWord ++ tailWord_397187).sum := by decide
  have hdescent : baseEnd_397187 < baseStart_397187 := by decide
  rcases family_descends (prefixWord ++ tailWord_397187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397217 : List Nat := [1, 2, 3, 4, 2, 1, 3, 1, 5]
def baseStart_397217 : Nat := 118140960795 + 397217 * 2 ^ 59
def prefixEnd_397217 : Nat := 4983230072969 + 3 ^ 40 * 397217 * 2
def baseEnd_397217 : Nat := 45325165586017248969053

theorem tailTrace_397217 : CollatzResearch.WordTrace tailWord_397217 prefixEnd_397217 45325165586017248969053 := by
  unfold tailWord_397217
  simp only [CollatzResearch.WordTrace]
  refine ⟨14487694201958123107749905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9658462801305415405166603 14487694201958123107749905)
  ·
    refine ⟨10865770651468592330812429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14487694201958123107749905 10865770651468592330812429)
    ·
      refine ⟨4074663994300722124054661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10865770651468592330812429 4074663994300722124054661)
      ·
        refine ⟨763999498931385398260249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4074663994300722124054661 763999498931385398260249)
        ·
          refine ⟨572999624198539048695187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 763999498931385398260249 572999624198539048695187)
          ·
            refine ⟨859499436297808573042781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572999624198539048695187 859499436297808573042781)
            ·
              refine ⟨322312288611678214891043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 859499436297808573042781 322312288611678214891043)
              ·
                refine ⟨483468432917517322336565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322312288611678214891043 483468432917517322336565)
                ·
                  refine ⟨45325165586017248969053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 483468432917517322336565 45325165586017248969053)
                  ·
                    rfl

theorem cell22_397217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 5].length) (baseStart_397217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397217 prefixEnd_397217 := by exact prefixLift 397217
  have htrace : WordTrace (prefixWord ++ tailWord_397217) baseStart_397217 baseEnd_397217 := by
    simpa [prefixWord, tailWord_397217, baseEnd_397217] using wordTrace_append hprefix tailTrace_397217
  have hstable : (prefixWord ++ tailWord_397217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397217).length < 2 ^ (prefixWord ++ tailWord_397217).sum := by decide
  have hdescent : baseEnd_397217 < baseStart_397217 := by decide
  rcases family_descends (prefixWord ++ tailWord_397217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397243 : List Nat := [1, 1, 1, 1, 1, 2, 2, 6, 4, 3]
def baseStart_397243 : Nat := 118140960795 + 397243 * 2 ^ 59
def prefixEnd_397243 : Nat := 4983230072969 + 3 ^ 40 * 397243 * 2
def baseEnd_397243 : Nat := 135984397089396345757079

theorem tailTrace_397243 : CollatzResearch.WordTrace tailWord_397243 prefixEnd_397243 135984397089396345757079 := by
  unfold tailWord_397243
  simp only [CollatzResearch.WordTrace]
  refine ⟨14488642499863929548196383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9659094999909286365464255 14488642499863929548196383)
  ·
    refine ⟨21732963749795894322294575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14488642499863929548196383 21732963749795894322294575)
    ·
      refine ⟨32599445624693841483441863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21732963749795894322294575 32599445624693841483441863)
      ·
        refine ⟨48899168437040762225162795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32599445624693841483441863 48899168437040762225162795)
        ·
          refine ⟨73348752655561143337744193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48899168437040762225162795 73348752655561143337744193)
          ·
            refine ⟨55011564491670857503308145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73348752655561143337744193 55011564491670857503308145)
            ·
              refine ⟨41258673368753143127481109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55011564491670857503308145 41258673368753143127481109)
              ·
                refine ⟨1934000314160303584100677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41258673368753143127481109 1934000314160303584100677)
                ·
                  refine ⟨362625058905056922018877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1934000314160303584100677 362625058905056922018877)
                  ·
                    refine ⟨135984397089396345757079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 362625058905056922018877 135984397089396345757079)
                    ·
                      rfl

theorem cell22_397243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4, 3].length) (baseStart_397243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397243 prefixEnd_397243 := by exact prefixLift 397243
  have htrace : WordTrace (prefixWord ++ tailWord_397243) baseStart_397243 baseEnd_397243 := by
    simpa [prefixWord, tailWord_397243, baseEnd_397243] using wordTrace_append hprefix tailTrace_397243
  have hstable : (prefixWord ++ tailWord_397243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397243).length < 2 ^ (prefixWord ++ tailWord_397243).sum := by decide
  have hdescent : baseEnd_397243 < baseStart_397243 := by decide
  rcases family_descends (prefixWord ++ tailWord_397243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397258 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 4, 4]
def baseStart_397258 : Nat := 118140960795 + 397258 * 2 ^ 59
def prefixEnd_397258 : Nat := 4983230072969 + 3 ^ 40 * 397258 * 2
def baseEnd_397258 : Nat := 135989531895941306632033

theorem tailTrace_397258 : CollatzResearch.WordTrace tailWord_397258 prefixEnd_397258 135989531895941306632033 := by
  unfold tailWord_397258
  simp only [CollatzResearch.WordTrace]
  refine ⟨3622297398702396777498107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9659459729873058073328285 3622297398702396777498107)
  ·
    refine ⟨5433446098053595166247161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3622297398702396777498107 5433446098053595166247161)
    ·
      refine ⟨4075084573540196374685371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5433446098053595166247161 4075084573540196374685371)
      ·
        refine ⟨6112626860310294562028057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4075084573540196374685371 6112626860310294562028057)
        ·
          refine ⟨4584470145232720921521043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6112626860310294562028057 4584470145232720921521043)
          ·
            refine ⟨6876705217849081382281565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4584470145232720921521043 6876705217849081382281565)
            ·
              refine ⟨2578764456693405518355587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6876705217849081382281565 2578764456693405518355587)
              ·
                refine ⟨3868146685040108277533381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2578764456693405518355587 3868146685040108277533381)
                ·
                  refine ⟨725277503445020302037509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3868146685040108277533381 725277503445020302037509)
                  ·
                    refine ⟨135989531895941306632033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 725277503445020302037509 135989531895941306632033)
                    ·
                      rfl

theorem cell22_397258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_397258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397258 prefixEnd_397258 := by exact prefixLift 397258
  have htrace : WordTrace (prefixWord ++ tailWord_397258) baseStart_397258 baseEnd_397258 := by
    simpa [prefixWord, tailWord_397258, baseEnd_397258] using wordTrace_append hprefix tailTrace_397258
  have hstable : (prefixWord ++ tailWord_397258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397258).length < 2 ^ (prefixWord ++ tailWord_397258).sum := by decide
  have hdescent : baseEnd_397258 < baseStart_397258 := by decide
  rcases family_descends (prefixWord ++ tailWord_397258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397260 : List Nat := [2, 2, 1, 4, 1, 2, 2, 1, 4, 3]
def baseStart_397260 : Nat := 118140960795 + 397260 * 2 ^ 59
def prefixEnd_397260 : Nat := 4983230072969 + 3 ^ 40 * 397260 * 2
def baseEnd_397260 : Nat := 135990216536813968082027

theorem tailTrace_397260 : CollatzResearch.WordTrace tailWord_397260 prefixEnd_397260 135990216536813968082027 := by
  unfold tailWord_397260
  simp only [CollatzResearch.WordTrace]
  refine ⟨7244631270401170725782617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9659508360534894301043489 7244631270401170725782617)
  ·
    refine ⟨5433473452800878044336963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7244631270401170725782617 5433473452800878044336963)
    ·
      refine ⟨8150210179201317066505445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5433473452800878044336963 8150210179201317066505445)
      ·
        refine ⟨1528164408600246949969771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8150210179201317066505445 1528164408600246949969771)
        ·
          refine ⟨2292246612900370424954657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1528164408600246949969771 2292246612900370424954657)
          ·
            refine ⟨1719184959675277818715993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2292246612900370424954657 1719184959675277818715993)
            ·
              refine ⟨1289388719756458364036995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1719184959675277818715993 1289388719756458364036995)
              ·
                refine ⟨1934083079634687546055493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1289388719756458364036995 1934083079634687546055493)
                ·
                  refine ⟨362640577431503914885405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1934083079634687546055493 362640577431503914885405)
                  ·
                    refine ⟨135990216536813968082027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 362640577431503914885405 135990216536813968082027)
                    ·
                      rfl

theorem cell22_397260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 4, 3].length) (baseStart_397260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397260 prefixEnd_397260 := by exact prefixLift 397260
  have htrace : WordTrace (prefixWord ++ tailWord_397260) baseStart_397260 baseEnd_397260 := by
    simpa [prefixWord, tailWord_397260, baseEnd_397260] using wordTrace_append hprefix tailTrace_397260
  have hstable : (prefixWord ++ tailWord_397260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397260).length < 2 ^ (prefixWord ++ tailWord_397260).sum := by decide
  have hdescent : baseEnd_397260 < baseStart_397260 := by decide
  rcases family_descends (prefixWord ++ tailWord_397260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397262 : List Nat := [4, 1, 1, 1, 2, 2, 5, 2, 4]
def baseStart_397262 : Nat := 118140960795 + 397262 * 2 ^ 59
def prefixEnd_397262 : Nat := 4983230072969 + 3 ^ 40 * 397262 * 2
def baseEnd_397262 : Nat := 45330300392562209844007

theorem tailTrace_397262 : CollatzResearch.WordTrace tailWord_397262 prefixEnd_397262 45330300392562209844007 := by
  unfold tailWord_397262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1811166935849386974142255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9659556991196730528758693 1811166935849386974142255)
  ·
    refine ⟨2716750403774080461213383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1811166935849386974142255 2716750403774080461213383)
    ·
      refine ⟨4075125605661120691820075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2716750403774080461213383 4075125605661120691820075)
      ·
        refine ⟨6112688408491681037730113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4075125605661120691820075 6112688408491681037730113)
        ·
          refine ⟨4584516306368760778297585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6112688408491681037730113 4584516306368760778297585)
          ·
            refine ⟨3438387229776570583723189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4584516306368760778297585 3438387229776570583723189)
            ·
              refine ⟨322348802791553492224049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3438387229776570583723189 322348802791553492224049)
              ·
                refine ⟨241761602093665119168037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322348802791553492224049 241761602093665119168037)
                ·
                  refine ⟨45330300392562209844007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 241761602093665119168037 45330300392562209844007)
                  ·
                    rfl

theorem cell22_397262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_397262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397262 prefixEnd_397262 := by exact prefixLift 397262
  have htrace : WordTrace (prefixWord ++ tailWord_397262) baseStart_397262 baseEnd_397262 := by
    simpa [prefixWord, tailWord_397262, baseEnd_397262] using wordTrace_append hprefix tailTrace_397262
  have hstable : (prefixWord ++ tailWord_397262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397262).length < 2 ^ (prefixWord ++ tailWord_397262).sum := by decide
  have hdescent : baseEnd_397262 < baseStart_397262 := by decide
  rcases family_descends (prefixWord ++ tailWord_397262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397369 : List Nat := [1, 2, 1, 5, 4, 1, 1, 2, 5]
def baseStart_397369 : Nat := 118140960795 + 397369 * 2 ^ 59
def prefixEnd_397369 : Nat := 4983230072969 + 3 ^ 40 * 397369 * 2
def baseEnd_397369 : Nat := 45342509821458005702231

theorem tailTrace_397369 : CollatzResearch.WordTrace tailWord_397369 prefixEnd_397369 45342509821458005702231 := by
  unfold tailWord_397369
  simp only [CollatzResearch.WordTrace]
  refine ⟨14493238097407453067283161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9662158731604968711522107 14493238097407453067283161)
  ·
    refine ⟨10869928573055589800462371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14493238097407453067283161 10869928573055589800462371)
    ·
      refine ⟨16304892859583384700693557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10869928573055589800462371 16304892859583384700693557)
      ·
        refine ⟨1528583705585942315690021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16304892859583384700693557 1528583705585942315690021)
        ·
          refine ⟨286609444797364184191879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1528583705585942315690021 286609444797364184191879)
          ·
            refine ⟨429914167196046276287819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286609444797364184191879 429914167196046276287819)
            ·
              refine ⟨644871250794069414431729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429914167196046276287819 644871250794069414431729)
              ·
                refine ⟨483653438095552060823797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 644871250794069414431729 483653438095552060823797)
                ·
                  refine ⟨45342509821458005702231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 483653438095552060823797 45342509821458005702231)
                  ·
                    rfl

theorem cell22_397369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 5].length) (baseStart_397369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397369 prefixEnd_397369 := by exact prefixLift 397369
  have htrace : WordTrace (prefixWord ++ tailWord_397369) baseStart_397369 baseEnd_397369 := by
    simpa [prefixWord, tailWord_397369, baseEnd_397369] using wordTrace_append hprefix tailTrace_397369
  have hstable : (prefixWord ++ tailWord_397369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397369).length < 2 ^ (prefixWord ++ tailWord_397369).sum := by decide
  have hdescent : baseEnd_397369 < baseStart_397369 := by decide
  rcases family_descends (prefixWord ++ tailWord_397369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397515 : List Nat := [1, 1, 1, 1, 3, 2, 5, 2, 6]
def baseStart_397515 : Nat := 118140960795 + 397515 * 2 ^ 59
def prefixEnd_397515 : Nat := 4983230072969 + 3 ^ 40 * 397515 * 2
def baseEnd_397515 : Nat := 45359169416026100985415

theorem tailTrace_397515 : CollatzResearch.WordTrace tailWord_397515 prefixEnd_397515 45359169416026100985415 := by
  unfold tailWord_397515
  simp only [CollatzResearch.WordTrace]
  refine ⟨14498563154878520002097999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9665708769919013334731999 14498563154878520002097999)
  ·
    refine ⟨21747844732317780003146999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14498563154878520002097999 21747844732317780003146999)
    ·
      refine ⟨32621767098476670004720499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21747844732317780003146999 32621767098476670004720499)
      ·
        refine ⟨48932650647715005007080749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32621767098476670004720499 48932650647715005007080749)
        ·
          refine ⟨18349743992893126877655281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48932650647715005007080749 18349743992893126877655281)
          ·
            refine ⟨13762307994669845158241461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18349743992893126877655281 13762307994669845158241461)
            ·
              refine ⟨1290216374500297983585137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13762307994669845158241461 1290216374500297983585137)
              ·
                refine ⟨967662280875223487688853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1290216374500297983585137 967662280875223487688853)
                ·
                  refine ⟨45359169416026100985415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 967662280875223487688853 45359169416026100985415)
                  ·
                    rfl

theorem cell22_397515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 6].length) (baseStart_397515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397515 prefixEnd_397515 := by exact prefixLift 397515
  have htrace : WordTrace (prefixWord ++ tailWord_397515) baseStart_397515 baseEnd_397515 := by
    simpa [prefixWord, tailWord_397515, baseEnd_397515] using wordTrace_append hprefix tailTrace_397515
  have hstable : (prefixWord ++ tailWord_397515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397515).length < 2 ^ (prefixWord ++ tailWord_397515).sum := by decide
  have hdescent : baseEnd_397515 < baseStart_397515 := by decide
  rcases family_descends (prefixWord ++ tailWord_397515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397547 : List Nat := [1, 1, 1, 1, 2, 5, 3, 1, 4, 3]
def baseStart_397547 : Nat := 118140960795 + 397547 * 2 ^ 59
def prefixEnd_397547 : Nat := 4983230072969 + 3 ^ 40 * 397547 * 2
def baseEnd_397547 : Nat := 136088462502040886156147

theorem tailTrace_397547 : CollatzResearch.WordTrace tailWord_397547 prefixEnd_397547 136088462502040886156147 := by
  unfold tailWord_397547
  simp only [CollatzResearch.WordTrace]
  refine ⟨14499730290762589467262895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9666486860508392978175263 14499730290762589467262895)
  ·
    refine ⟨21749595436143884200894343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14499730290762589467262895 21749595436143884200894343)
    ·
      refine ⟨32624393154215826301341515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21749595436143884200894343 32624393154215826301341515)
      ·
        refine ⟨48936589731323739452012273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32624393154215826301341515 48936589731323739452012273)
        ·
          refine ⟨36702442298492804589009205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48936589731323739452012273 36702442298492804589009205)
          ·
            refine ⟨3440853965483700430219613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36702442298492804589009205 3440853965483700430219613)
            ·
              refine ⟨1290320237056387661332355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3440853965483700430219613 1290320237056387661332355)
              ·
                refine ⟨1935480355584581491998533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1290320237056387661332355 1935480355584581491998533)
                ·
                  refine ⟨362902566672109029749725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1935480355584581491998533 362902566672109029749725)
                  ·
                    refine ⟨136088462502040886156147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 362902566672109029749725 136088462502040886156147)
                    ·
                      rfl

theorem cell22_397547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4, 3].length) (baseStart_397547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397547 prefixEnd_397547 := by exact prefixLift 397547
  have htrace : WordTrace (prefixWord ++ tailWord_397547) baseStart_397547 baseEnd_397547 := by
    simpa [prefixWord, tailWord_397547, baseEnd_397547] using wordTrace_append hprefix tailTrace_397547
  have hstable : (prefixWord ++ tailWord_397547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397547).length < 2 ^ (prefixWord ++ tailWord_397547).sum := by decide
  have hdescent : baseEnd_397547 < baseStart_397547 := by decide
  rcases family_descends (prefixWord ++ tailWord_397547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397549 : List Nat := [1, 5, 1, 2, 3, 1, 2, 1, 6]
def baseStart_397549 : Nat := 118140960795 + 397549 * 2 ^ 59
def prefixEnd_397549 : Nat := 4983230072969 + 3 ^ 40 * 397549 * 2
def baseEnd_397549 : Nat := 45363049047637849202047

theorem tailTrace_397549 : CollatzResearch.WordTrace tailWord_397549 prefixEnd_397549 45363049047637849202047 := by
  unfold tailWord_397549
  simp only [CollatzResearch.WordTrace]
  refine ⟨14499803236755343808835701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9666535491170229205890467 14499803236755343808835701)
  ·
    refine ⟨1359356553445813482078347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14499803236755343808835701 1359356553445813482078347)
    ·
      refine ⟨2039034830168720223117521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1359356553445813482078347 2039034830168720223117521)
      ·
        refine ⟨1529276122626540167338141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2039034830168720223117521 1529276122626540167338141)
        ·
          refine ⟨573478545984952562751803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1529276122626540167338141 573478545984952562751803)
          ·
            refine ⟨860217818977428844127705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573478545984952562751803 860217818977428844127705)
            ·
              refine ⟨645163364233071633095779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 860217818977428844127705 645163364233071633095779)
              ·
                refine ⟨967745046349607449643669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645163364233071633095779 967745046349607449643669)
                ·
                  refine ⟨45363049047637849202047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 967745046349607449643669 45363049047637849202047)
                  ·
                    rfl

theorem cell22_397549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_397549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397549 prefixEnd_397549 := by exact prefixLift 397549
  have htrace : WordTrace (prefixWord ++ tailWord_397549) baseStart_397549 baseEnd_397549 := by
    simpa [prefixWord, tailWord_397549, baseEnd_397549] using wordTrace_append hprefix tailTrace_397549
  have hstable : (prefixWord ++ tailWord_397549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397549).length < 2 ^ (prefixWord ++ tailWord_397549).sum := by decide
  have hdescent : baseEnd_397549 < baseStart_397549 := by decide
  rcases family_descends (prefixWord ++ tailWord_397549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397564 : List Nat := [2, 2, 2, 1, 4, 3, 1, 1, 1, 5]
def baseStart_397564 : Nat := 118140960795 + 397564 * 2 ^ 59
def prefixEnd_397564 : Nat := 4983230072969 + 3 ^ 40 * 397564 * 2
def baseEnd_397564 : Nat := 136094281949458508481095

theorem tailTrace_397564 : CollatzResearch.WordTrace tailWord_397564 prefixEnd_397564 136094281949458508481095 := by
  unfold tailWord_397564
  simp only [CollatzResearch.WordTrace]
  refine ⟨7250175165850500685315873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9666900221134000913754497 7250175165850500685315873)
  ·
    refine ⟨5437631374387875513986905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7250175165850500685315873 5437631374387875513986905)
    ·
      refine ⟨4078223530790906635490179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5437631374387875513986905 4078223530790906635490179)
      ·
        refine ⟨6117335296186359953235269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4078223530790906635490179 6117335296186359953235269)
        ·
          refine ⟨1147000368034942491231613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6117335296186359953235269 1147000368034942491231613)
          ·
            refine ⟨430125138013103434211855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1147000368034942491231613 430125138013103434211855)
            ·
              refine ⟨645187707019655151317783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430125138013103434211855 645187707019655151317783)
              ·
                refine ⟨967781560529482726976675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645187707019655151317783 967781560529482726976675)
                ·
                  refine ⟨1451672340794224090465013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 967781560529482726976675 1451672340794224090465013)
                  ·
                    refine ⟨136094281949458508481095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1451672340794224090465013 136094281949458508481095)
                    ·
                      rfl

theorem cell22_397564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_397564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397564 prefixEnd_397564 := by exact prefixLift 397564
  have htrace : WordTrace (prefixWord ++ tailWord_397564) baseStart_397564 baseEnd_397564 := by
    simpa [prefixWord, tailWord_397564, baseEnd_397564] using wordTrace_append hprefix tailTrace_397564
  have hstable : (prefixWord ++ tailWord_397564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397564).length < 2 ^ (prefixWord ++ tailWord_397564).sum := by decide
  have hdescent : baseEnd_397564 < baseStart_397564 := by decide
  rcases family_descends (prefixWord ++ tailWord_397564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397577 : List Nat := [1, 2, 1, 1, 3, 4, 4, 6]
def baseStart_397577 : Nat := 118140960795 + 397577 * 2 ^ 59
def prefixEnd_397577 : Nat := 4983230072969 + 3 ^ 40 * 397577 * 2
def baseEnd_397577 : Nat := 15122081346125645322895

theorem tailTrace_397577 : CollatzResearch.WordTrace tailWord_397577 prefixEnd_397577 15122081346125645322895 := by
  unfold tailWord_397577
  simp only [CollatzResearch.WordTrace]
  refine ⟨14500824480653904590854985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9667216320435936393903323 14500824480653904590854985)
  ·
    refine ⟨10875618360490428443141239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14500824480653904590854985 10875618360490428443141239)
    ·
      refine ⟨16313427540735642664711859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10875618360490428443141239 16313427540735642664711859)
      ·
        refine ⟨24470141311103463997067789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16313427540735642664711859 24470141311103463997067789)
        ·
          refine ⟨9176302991663798998900421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24470141311103463997067789 9176302991663798998900421)
          ·
            refine ⟨1720556810936962312293829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9176302991663798998900421 1720556810936962312293829)
            ·
              refine ⟨322604402050680433555093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1720556810936962312293829 322604402050680433555093)
              ·
                refine ⟨15122081346125645322895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 322604402050680433555093 15122081346125645322895)
                ·
                  rfl

theorem cell22_397577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 6].length) (baseStart_397577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397577 prefixEnd_397577 := by exact prefixLift 397577
  have htrace : WordTrace (prefixWord ++ tailWord_397577) baseStart_397577 baseEnd_397577 := by
    simpa [prefixWord, tailWord_397577, baseEnd_397577] using wordTrace_append hprefix tailTrace_397577
  have hstable : (prefixWord ++ tailWord_397577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397577).length < 2 ^ (prefixWord ++ tailWord_397577).sum := by decide
  have hdescent : baseEnd_397577 < baseStart_397577 := by decide
  rcases family_descends (prefixWord ++ tailWord_397577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397594 : List Nat := [3, 1, 1, 3, 5, 1, 8]
def baseStart_397594 : Nat := 118140960795 + 397594 * 2 ^ 59
def prefixEnd_397594 : Nat := 4983230072969 + 3 ^ 40 * 397594 * 2
def baseEnd_397594 : Nat := 5040909317131423341889

theorem tailTrace_397594 : CollatzResearch.WordTrace tailWord_397594 prefixEnd_397594 5040909317131423341889 := by
  unfold tailWord_397594
  simp only [CollatzResearch.WordTrace]
  refine ⟨3625361130398079123555959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9667629681061544329482557 3625361130398079123555959)
  ·
    refine ⟨5438041695597118685333939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3625361130398079123555959 5438041695597118685333939)
    ·
      refine ⟨8157062543395678028000909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5438041695597118685333939 8157062543395678028000909)
      ·
        refine ⟨3058898453773379260500341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8157062543395678028000909 3058898453773379260500341)
        ·
          refine ⟨286771730041254305671907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3058898453773379260500341 286771730041254305671907)
          ·
            refine ⟨430157595061881458507861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286771730041254305671907 430157595061881458507861)
            ·
              refine ⟨5040909317131423341889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 430157595061881458507861 5040909317131423341889)
              ·
                rfl

theorem cell22_397594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 8].length) (baseStart_397594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397594 prefixEnd_397594 := by exact prefixLift 397594
  have htrace : WordTrace (prefixWord ++ tailWord_397594) baseStart_397594 baseEnd_397594 := by
    simpa [prefixWord, tailWord_397594, baseEnd_397594] using wordTrace_append hprefix tailTrace_397594
  have hstable : (prefixWord ++ tailWord_397594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397594).length < 2 ^ (prefixWord ++ tailWord_397594).sum := by decide
  have hdescent : baseEnd_397594 < baseStart_397594 := by decide
  rcases family_descends (prefixWord ++ tailWord_397594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397660 : List Nat := [2, 2, 4, 3, 1, 1, 1, 4, 1, 3]
def baseStart_397660 : Nat := 118140960795 + 397660 * 2 ^ 59
def prefixEnd_397660 : Nat := 4983230072969 + 3 ^ 40 * 397660 * 2
def baseEnd_397660 : Nat := 136127144711346258080801

theorem tailTrace_397660 : CollatzResearch.WordTrace tailWord_397660 prefixEnd_397660 136127144711346258080801 := by
  unfold tailWord_397660
  simp only [CollatzResearch.WordTrace]
  refine ⟨7251925869676604883063217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9669234492902139844084289 7251925869676604883063217)
  ·
    refine ⟨5438944402257453662297413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7251925869676604883063217 5438944402257453662297413)
    ·
      refine ⟨1019802075423272561680765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5438944402257453662297413 1019802075423272561680765)
      ·
        refine ⟨382425778283727210630287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1019802075423272561680765 382425778283727210630287)
        ·
          refine ⟨573638667425590815945431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382425778283727210630287 573638667425590815945431)
          ·
            refine ⟨860458001138386223918147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573638667425590815945431 860458001138386223918147)
            ·
              refine ⟨1290687001707579335877221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 860458001138386223918147 1290687001707579335877221)
              ·
                refine ⟨242003812820171125476979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1290687001707579335877221 242003812820171125476979)
                ·
                  refine ⟨363005719230256688215469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 242003812820171125476979 363005719230256688215469)
                  ·
                    refine ⟨136127144711346258080801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 363005719230256688215469 136127144711346258080801)
                    ·
                      rfl

theorem cell22_397660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_397660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397660 prefixEnd_397660 := by exact prefixLift 397660
  have htrace : WordTrace (prefixWord ++ tailWord_397660) baseStart_397660 baseEnd_397660 := by
    simpa [prefixWord, tailWord_397660, baseEnd_397660] using wordTrace_append hprefix tailTrace_397660
  have hstable : (prefixWord ++ tailWord_397660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397660).length < 2 ^ (prefixWord ++ tailWord_397660).sum := by decide
  have hdescent : baseEnd_397660 < baseStart_397660 := by decide
  rcases family_descends (prefixWord ++ tailWord_397660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397662 : List Nat := [4, 4, 2, 1, 2, 1, 1, 7]
def baseStart_397662 : Nat := 118140960795 + 397662 * 2 ^ 59
def prefixEnd_397662 : Nat := 4983230072969 + 3 ^ 40 * 397662 * 2
def baseEnd_397662 : Nat := 15125314372468768836755

theorem tailTrace_397662 : CollatzResearch.WordTrace tailWord_397662 prefixEnd_397662 15125314372468768836755 := by
  unfold tailWord_397662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1812990585668245513462405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9669283123563976071799493 1812990585668245513462405)
  ·
    refine ⟨339935734812796033774201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1812990585668245513462405 339935734812796033774201)
    ·
      refine ⟨254951801109597025330651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339935734812796033774201 254951801109597025330651)
      ·
        refine ⟨382427701664395537995977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254951801109597025330651 382427701664395537995977)
        ·
          refine ⟨286820776248296653496983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382427701664395537995977 286820776248296653496983)
          ·
            refine ⟨430231164372444980245475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286820776248296653496983 430231164372444980245475)
            ·
              refine ⟨645346746558667470368213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430231164372444980245475 645346746558667470368213)
              ·
                refine ⟨15125314372468768836755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 645346746558667470368213 15125314372468768836755)
                ·
                  rfl

theorem cell22_397662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 7].length) (baseStart_397662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397662 prefixEnd_397662 := by exact prefixLift 397662
  have htrace : WordTrace (prefixWord ++ tailWord_397662) baseStart_397662 baseEnd_397662 := by
    simpa [prefixWord, tailWord_397662, baseEnd_397662] using wordTrace_append hprefix tailTrace_397662
  have hstable : (prefixWord ++ tailWord_397662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397662).length < 2 ^ (prefixWord ++ tailWord_397662).sum := by decide
  have hdescent : baseEnd_397662 < baseStart_397662 := by decide
  rcases family_descends (prefixWord ++ tailWord_397662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397667 : List Nat := [1, 1, 1, 5, 2, 1, 2, 3, 6]
def baseStart_397667 : Nat := 118140960795 + 397667 * 2 ^ 59
def prefixEnd_397667 : Nat := 4983230072969 + 3 ^ 40 * 397667 * 2
def baseEnd_397667 : Nat := 45376513651466857718593

theorem tailTrace_397667 : CollatzResearch.WordTrace tailWord_397667 prefixEnd_397667 45376513651466857718593 := by
  unfold tailWord_397667
  simp only [CollatzResearch.WordTrace]
  refine ⟨14504107050327849961631255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9669404700218566641087503 14504107050327849961631255)
  ·
    refine ⟨21756160575491774942446883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14504107050327849961631255 21756160575491774942446883)
    ·
      refine ⟨32634240863237662413670325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21756160575491774942446883 32634240863237662413670325)
      ·
        refine ⟨3059460080928530851281593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32634240863237662413670325 3059460080928530851281593)
        ·
          refine ⟨2294595060696398138461195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3059460080928530851281593 2294595060696398138461195)
          ·
            refine ⟨3441892591044597207691793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2294595060696398138461195 3441892591044597207691793)
            ·
              refine ⟨2581419443283447905768845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3441892591044597207691793 2581419443283447905768845)
              ·
                refine ⟨968032291231292964663317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2581419443283447905768845 968032291231292964663317)
                ·
                  refine ⟨45376513651466857718593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 968032291231292964663317 45376513651466857718593)
                  ·
                    rfl

theorem cell22_397667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 6].length) (baseStart_397667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397667 prefixEnd_397667 := by exact prefixLift 397667
  have htrace : WordTrace (prefixWord ++ tailWord_397667) baseStart_397667 baseEnd_397667 := by
    simpa [prefixWord, tailWord_397667, baseEnd_397667] using wordTrace_append hprefix tailTrace_397667
  have hstable : (prefixWord ++ tailWord_397667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397667).length < 2 ^ (prefixWord ++ tailWord_397667).sum := by decide
  have hdescent : baseEnd_397667 < baseStart_397667 := by decide
  rcases family_descends (prefixWord ++ tailWord_397667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397774 : List Nat := [4, 1, 1, 1, 2, 1, 1, 6, 5]
def baseStart_397774 : Nat := 118140960795 + 397774 * 2 ^ 59
def prefixEnd_397774 : Nat := 4983230072969 + 3 ^ 40 * 397774 * 2
def baseEnd_397774 : Nat := 45388723080362653576817

theorem tailTrace_397774 : CollatzResearch.WordTrace tailWord_397774 prefixEnd_397774 45388723080362653576817 := by
  unfold tailWord_397774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1813501207617525904472047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9672006440626804823850917 1813501207617525904472047)
  ·
    refine ⟨2720251811426288856708071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1813501207617525904472047 2720251811426288856708071)
    ·
      refine ⟨4080377717139433285062107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2720251811426288856708071 4080377717139433285062107)
      ·
        refine ⟨6120566575709149927593161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4080377717139433285062107 6120566575709149927593161)
        ·
          refine ⟨4590424931781862445694871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6120566575709149927593161 4590424931781862445694871)
          ·
            refine ⟨6885637397672793668542307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4590424931781862445694871 6885637397672793668542307)
            ·
              refine ⟨10328456096509190502813461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6885637397672793668542307 10328456096509190502813461)
              ·
                refine ⟨484146379523868304819381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10328456096509190502813461 484146379523868304819381)
                ·
                  refine ⟨45388723080362653576817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 484146379523868304819381 45388723080362653576817)
                  ·
                    rfl

theorem cell22_397774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_397774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397774 prefixEnd_397774 := by exact prefixLift 397774
  have htrace : WordTrace (prefixWord ++ tailWord_397774) baseStart_397774 baseEnd_397774 := by
    simpa [prefixWord, tailWord_397774, baseEnd_397774] using wordTrace_append hprefix tailTrace_397774
  have hstable : (prefixWord ++ tailWord_397774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397774).length < 2 ^ (prefixWord ++ tailWord_397774).sum := by decide
  have hdescent : baseEnd_397774 < baseStart_397774 := by decide
  rcases family_descends (prefixWord ++ tailWord_397774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397789 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 1, 7]
def baseStart_397789 : Nat := 118140960795 + 397789 * 2 ^ 59
def prefixEnd_397789 : Nat := 4983230072969 + 3 ^ 40 * 397789 * 2
def baseEnd_397789 : Nat := 136171304047632921605405

theorem tailTrace_397789 : CollatzResearch.WordTrace tailWord_397789 prefixEnd_397789 136171304047632921605405 := by
  unfold tailWord_397789
  simp only [CollatzResearch.WordTrace]
  refine ⟨14508556755885864797572421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9672371170590576531714947 14508556755885864797572421)
  ·
    refine ⟨2720354391728599649544829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14508556755885864797572421 2720354391728599649544829)
    ·
      refine ⟨1020132896898224868579311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2720354391728599649544829 1020132896898224868579311)
      ·
        refine ⟨1530199345347337302868967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1020132896898224868579311 1530199345347337302868967)
        ·
          refine ⟨2295299018021005954303451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1530199345347337302868967 2295299018021005954303451)
          ·
            refine ⟨3442948527031508931455177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2295299018021005954303451 3442948527031508931455177)
            ·
              refine ⟨2582211395273631698591383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3442948527031508931455177 2582211395273631698591383)
              ·
                refine ⟨3873317092910447547887075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2582211395273631698591383 3873317092910447547887075)
                ·
                  refine ⟨5809975639365671321830613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3873317092910447547887075 5809975639365671321830613)
                  ·
                    refine ⟨136171304047632921605405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5809975639365671321830613 136171304047632921605405)
                    ·
                      rfl

theorem cell22_397789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_397789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397789 prefixEnd_397789 := by exact prefixLift 397789
  have htrace : WordTrace (prefixWord ++ tailWord_397789) baseStart_397789 baseEnd_397789 := by
    simpa [prefixWord, tailWord_397789, baseEnd_397789] using wordTrace_append hprefix tailTrace_397789
  have hstable : (prefixWord ++ tailWord_397789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397789).length < 2 ^ (prefixWord ++ tailWord_397789).sum := by decide
  have hdescent : baseEnd_397789 < baseStart_397789 := by decide
  rcases family_descends (prefixWord ++ tailWord_397789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397791 : List Nat := [1, 1, 2, 3, 3, 2, 4, 1, 5]
def baseStart_397791 : Nat := 118140960795 + 397791 * 2 ^ 59
def prefixEnd_397791 : Nat := 4983230072969 + 3 ^ 40 * 397791 * 2
def baseEnd_397791 : Nat := 45390662896168527685133

theorem tailTrace_397791 : CollatzResearch.WordTrace tailWord_397791 prefixEnd_397791 45390662896168527685133 := by
  unfold tailWord_397791
  simp only [CollatzResearch.WordTrace]
  refine ⟨14508629701878619139145227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9672419801252412759430151 14508629701878619139145227)
  ·
    refine ⟨21762944552817928708717841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14508629701878619139145227 21762944552817928708717841)
    ·
      refine ⟨16322208414613446531538381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21762944552817928708717841 16322208414613446531538381)
      ·
        refine ⟨6120828155480042449326893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16322208414613446531538381 6120828155480042449326893)
        ·
          refine ⟨2295310558305015918497585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6120828155480042449326893 2295310558305015918497585)
          ·
            refine ⟨1721482918728761938873189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2295310558305015918497585 1721482918728761938873189)
            ·
              refine ⟨322778047261642863538723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1721482918728761938873189 322778047261642863538723)
              ·
                refine ⟨484167070892464295308085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322778047261642863538723 484167070892464295308085)
                ·
                  refine ⟨45390662896168527685133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 484167070892464295308085 45390662896168527685133)
                  ·
                    rfl

theorem cell22_397791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 5].length) (baseStart_397791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397791 prefixEnd_397791 := by exact prefixLift 397791
  have htrace : WordTrace (prefixWord ++ tailWord_397791) baseStart_397791 baseEnd_397791 := by
    simpa [prefixWord, tailWord_397791, baseEnd_397791] using wordTrace_append hprefix tailTrace_397791
  have hstable : (prefixWord ++ tailWord_397791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397791).length < 2 ^ (prefixWord ++ tailWord_397791).sum := by decide
  have hdescent : baseEnd_397791 < baseStart_397791 := by decide
  rcases family_descends (prefixWord ++ tailWord_397791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397804 : List Nat := [2, 2, 1, 1, 2, 1, 5, 1, 3, 4]
def baseStart_397804 : Nat := 118140960795 + 397804 * 2 ^ 59
def prefixEnd_397804 : Nat := 4983230072969 + 3 ^ 40 * 397804 * 2
def baseEnd_397804 : Nat := 136176438854177882480359

theorem tailTrace_397804 : CollatzResearch.WordTrace tailWord_397804 prefixEnd_397804 136176438854177882480359 := by
  unfold tailWord_397804
  simp only [CollatzResearch.WordTrace]
  refine ⟨7254551925415761179684233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9672735900554348239578977 7254551925415761179684233)
  ·
    refine ⟨5440913944061820884763175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7254551925415761179684233 5440913944061820884763175)
    ·
      refine ⟨8161370916092731327144763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5440913944061820884763175 8161370916092731327144763)
      ·
        refine ⟨12242056374139096990717145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8161370916092731327144763 12242056374139096990717145)
        ·
          refine ⟨9181542280604322743037859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12242056374139096990717145 9181542280604322743037859)
          ·
            refine ⟨13772313420906484114556789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9181542280604322743037859 13772313420906484114556789)
            ·
              refine ⟨1291154383209982885739699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13772313420906484114556789 1291154383209982885739699)
              ·
                refine ⟨1936731574814974328609549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1291154383209982885739699 1936731574814974328609549)
                ·
                  refine ⟨726274340555615373228581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1936731574814974328609549 726274340555615373228581)
                  ·
                    refine ⟨136176438854177882480359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 726274340555615373228581 136176438854177882480359)
                    ·
                      rfl

theorem cell22_397804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_397804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397804 prefixEnd_397804 := by exact prefixLift 397804
  have htrace : WordTrace (prefixWord ++ tailWord_397804) baseStart_397804 baseEnd_397804 := by
    simpa [prefixWord, tailWord_397804, baseEnd_397804] using wordTrace_append hprefix tailTrace_397804
  have hstable : (prefixWord ++ tailWord_397804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397804).length < 2 ^ (prefixWord ++ tailWord_397804).sum := by decide
  have hdescent : baseEnd_397804 < baseStart_397804 := by decide
  rcases family_descends (prefixWord ++ tailWord_397804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397834 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 3, 5]
def baseStart_397834 : Nat := 118140960795 + 397834 * 2 ^ 59
def prefixEnd_397834 : Nat := 4983230072969 + 3 ^ 40 * 397834 * 2
def baseEnd_397834 : Nat := 136186708467267804230267

theorem tailTrace_397834 : CollatzResearch.WordTrace tailWord_397834 prefixEnd_397834 136186708467267804230267 := by
  unfold tailWord_397834
  simp only [CollatzResearch.WordTrace]
  refine ⟨3627549510180709370740139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9673465360481891655307037 3627549510180709370740139)
  ·
    refine ⟨5441324265271064056110209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3627549510180709370740139 5441324265271064056110209)
    ·
      refine ⟨4080993198953298042082657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5441324265271064056110209 4080993198953298042082657)
      ·
        refine ⟨3060744899214973531561993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4080993198953298042082657 3060744899214973531561993)
        ·
          refine ⟨2295558674411230148671495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3060744899214973531561993 2295558674411230148671495)
          ·
            refine ⟨3443338011616845223007243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2295558674411230148671495 3443338011616845223007243)
            ·
              refine ⟨5165007017425267834510865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3443338011616845223007243 5165007017425267834510865)
              ·
                refine ⟨3873755263068950875883149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5165007017425267834510865 3873755263068950875883149)
                ·
                  refine ⟨1452658223650856578456181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3873755263068950875883149 1452658223650856578456181)
                  ·
                    refine ⟨136186708467267804230267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1452658223650856578456181 136186708467267804230267)
                    ·
                      rfl

theorem cell22_397834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_397834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397834 prefixEnd_397834 := by exact prefixLift 397834
  have htrace : WordTrace (prefixWord ++ tailWord_397834) baseStart_397834 baseEnd_397834 := by
    simpa [prefixWord, tailWord_397834, baseEnd_397834] using wordTrace_append hprefix tailTrace_397834
  have hstable : (prefixWord ++ tailWord_397834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397834).length < 2 ^ (prefixWord ++ tailWord_397834).sum := by decide
  have hdescent : baseEnd_397834 < baseStart_397834 := by decide
  rcases family_descends (prefixWord ++ tailWord_397834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397866 : List Nat := [3, 1, 4, 1, 1, 3, 1, 1, 1, 6]
def baseStart_397866 : Nat := 118140960795 + 397866 * 2 ^ 59
def prefixEnd_397866 : Nat := 4983230072969 + 3 ^ 40 * 397866 * 2
def baseEnd_397866 : Nat := 136197662721230387430169

theorem tailTrace_397866 : CollatzResearch.WordTrace tailWord_397866 prefixEnd_397866 136197662721230387430169 := by
  unfold tailWord_397866
  simp only [CollatzResearch.WordTrace]
  refine ⟨3627841294151726737031363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9674243451071271298750301 3627841294151726737031363)
  ·
    refine ⟨5441761941227590105547045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3627841294151726737031363 5441761941227590105547045)
    ·
      refine ⟨1020330363980173144790071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5441761941227590105547045 1020330363980173144790071)
      ·
        refine ⟨1530495545970259717185107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1020330363980173144790071 1530495545970259717185107)
        ·
          refine ⟨2295743318955389575777661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1530495545970259717185107 2295743318955389575777661)
          ·
            refine ⟨860903744608271090916623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2295743318955389575777661 860903744608271090916623)
            ·
              refine ⟨1291355616912406636374935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 860903744608271090916623 1291355616912406636374935)
              ·
                refine ⟨1937033425368609954562403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1291355616912406636374935 1937033425368609954562403)
                ·
                  refine ⟨2905550138052914931843605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1937033425368609954562403 2905550138052914931843605)
                  ·
                    refine ⟨136197662721230387430169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2905550138052914931843605 136197662721230387430169)
                    ·
                      rfl

theorem cell22_397866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_397866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397866 prefixEnd_397866 := by exact prefixLift 397866
  have htrace : WordTrace (prefixWord ++ tailWord_397866) baseStart_397866 baseEnd_397866 := by
    simpa [prefixWord, tailWord_397866, baseEnd_397866] using wordTrace_append hprefix tailTrace_397866
  have hstable : (prefixWord ++ tailWord_397866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397866).length < 2 ^ (prefixWord ++ tailWord_397866).sum := by decide
  have hdescent : baseEnd_397866 < baseStart_397866 := by decide
  rcases family_descends (prefixWord ++ tailWord_397866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397870 : List Nat := [4, 1, 3, 1, 3, 1, 2, 3, 4]
def baseStart_397870 : Nat := 118140960795 + 397870 * 2 ^ 59
def prefixEnd_397870 : Nat := 4983230072969 + 3 ^ 40 * 397870 * 2
def baseEnd_397870 : Nat := 45399677334325236776719

theorem tailTrace_397870 : CollatzResearch.WordTrace tailWord_397870 prefixEnd_397870 45399677334325236776719 := by
  unfold tailWord_397870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1813938883574051953908883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9674340712394943754180709 1813938883574051953908883)
  ·
    refine ⟨2720908325361077930863325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1813938883574051953908883 2720908325361077930863325)
    ·
      refine ⟨1020340622010404224073747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2720908325361077930863325 1020340622010404224073747)
      ·
        refine ⟨1530510933015606336110621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1020340622010404224073747 1530510933015606336110621)
        ·
          refine ⟨573941599880852376041483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1530510933015606336110621 573941599880852376041483)
          ·
            refine ⟨860912399821278564062225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573941599880852376041483 860912399821278564062225)
            ·
              refine ⟨645684299865958923046669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 860912399821278564062225 645684299865958923046669)
              ·
                refine ⟨242131612449734596142501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 645684299865958923046669 242131612449734596142501)
                ·
                  refine ⟨45399677334325236776719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 242131612449734596142501 45399677334325236776719)
                  ·
                    rfl

theorem cell22_397870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_397870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397870 prefixEnd_397870 := by exact prefixLift 397870
  have htrace : WordTrace (prefixWord ++ tailWord_397870) baseStart_397870 baseEnd_397870 := by
    simpa [prefixWord, tailWord_397870, baseEnd_397870] using wordTrace_append hprefix tailTrace_397870
  have hstable : (prefixWord ++ tailWord_397870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397870).length < 2 ^ (prefixWord ++ tailWord_397870).sum := by decide
  have hdescent : baseEnd_397870 < baseStart_397870 := by decide
  rcases family_descends (prefixWord ++ tailWord_397870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397885 : List Nat := [1, 4, 1, 3, 2, 3, 1, 2, 2, 3]
def baseStart_397885 : Nat := 118140960795 + 397885 * 2 ^ 59
def prefixEnd_397885 : Nat := 4983230072969 + 3 ^ 40 * 397885 * 2
def baseEnd_397885 : Nat := 136204166809520671205111

theorem tailTrace_397885 : CollatzResearch.WordTrace tailWord_397885 prefixEnd_397885 136204166809520671205111 := by
  unfold tailWord_397885
  simp only [CollatzResearch.WordTrace]
  refine ⟨14512058163538073193067109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9674705442358715462044739 14512058163538073193067109)
  ·
    refine ⟨2721010905663388723700083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14512058163538073193067109 2721010905663388723700083)
    ·
      refine ⟨4081516358495083085550125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2721010905663388723700083 4081516358495083085550125)
      ·
        refine ⟨1530568634435656157081297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4081516358495083085550125 1530568634435656157081297)
        ·
          refine ⟨1147926475826742117810973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1530568634435656157081297 1147926475826742117810973)
          ·
            refine ⟨430472428435028294179115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1147926475826742117810973 430472428435028294179115)
            ·
              refine ⟨645708642652542441268673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430472428435028294179115 645708642652542441268673)
              ·
                refine ⟨484281481989406830951505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 645708642652542441268673 484281481989406830951505)
                ·
                  refine ⟨363211111492055123213629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484281481989406830951505 363211111492055123213629)
                  ·
                    refine ⟨136204166809520671205111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 363211111492055123213629 136204166809520671205111)
                    ·
                      rfl

theorem cell22_397885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_397885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397885 prefixEnd_397885 := by exact prefixLift 397885
  have htrace : WordTrace (prefixWord ++ tailWord_397885) baseStart_397885 baseEnd_397885 := by
    simpa [prefixWord, tailWord_397885, baseEnd_397885] using wordTrace_append hprefix tailTrace_397885
  have hstable : (prefixWord ++ tailWord_397885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397885).length < 2 ^ (prefixWord ++ tailWord_397885).sum := by decide
  have hdescent : baseEnd_397885 < baseStart_397885 := by decide
  rcases family_descends (prefixWord ++ tailWord_397885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397988 : List Nat := [2, 3, 1, 2, 2, 1, 2, 5, 4]
def baseStart_397988 : Nat := 118140960795 + 397988 * 2 ^ 59
def prefixEnd_397988 : Nat := 4983230072969 + 3 ^ 40 * 397988 * 2
def baseEnd_397988 : Nat := 45413141938154245293265

theorem tailTrace_397988 : CollatzResearch.WordTrace tailWord_397988 prefixEnd_397988 45413141938154245293265 := by
  unfold tailWord_397988
  simp only [CollatzResearch.WordTrace]
  refine ⟨7257907441082460892033309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9677209921443281189377745 7257907441082460892033309)
  ·
    refine ⟨2721715290405922834512491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7257907441082460892033309 2721715290405922834512491)
    ·
      refine ⟨4082572935608884251768737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2721715290405922834512491 4082572935608884251768737)
      ·
        refine ⟨3061929701706663188826553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4082572935608884251768737 3061929701706663188826553)
        ·
          refine ⟨2296447276279997391619915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3061929701706663188826553 2296447276279997391619915)
          ·
            refine ⟨3444670914419996087429873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2296447276279997391619915 3444670914419996087429873)
            ·
              refine ⟨2583503185814997065572405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3444670914419996087429873 2583503185814997065572405)
              ·
                refine ⟨242203423670155974897413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2583503185814997065572405 242203423670155974897413)
                ·
                  refine ⟨45413141938154245293265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 242203423670155974897413 45413141938154245293265)
                  ·
                    rfl

theorem cell22_397988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_397988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397988 prefixEnd_397988 := by exact prefixLift 397988
  have htrace : WordTrace (prefixWord ++ tailWord_397988) baseStart_397988 baseEnd_397988 := by
    simpa [prefixWord, tailWord_397988, baseEnd_397988] using wordTrace_append hprefix tailTrace_397988
  have hstable : (prefixWord ++ tailWord_397988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397988).length < 2 ^ (prefixWord ++ tailWord_397988).sum := by decide
  have hdescent : baseEnd_397988 < baseStart_397988 := by decide
  rcases family_descends (prefixWord ++ tailWord_397988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397999 : List Nat := [1, 1, 2, 1, 2, 15]
def baseStart_397999 : Nat := 118140960795 + 397999 * 2 ^ 59
def prefixEnd_397999 : Nat := 4983230072969 + 3 ^ 40 * 397999 * 2
def baseEnd_397999 : Nat := 1682014707892128072281

theorem tailTrace_397999 : CollatzResearch.WordTrace tailWord_397999 prefixEnd_397999 1682014707892128072281 := by
  unfold tailWord_397999
  simp only [CollatzResearch.WordTrace]
  refine ⟨14516216085125070662717051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9677477390083380441811367 14516216085125070662717051)
  ·
    refine ⟨21774324127687605994075577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14516216085125070662717051 21774324127687605994075577)
    ·
      refine ⟨16330743095765704495556683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21774324127687605994075577 16330743095765704495556683)
      ·
        refine ⟨24496114643648556743335025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16330743095765704495556683 24496114643648556743335025)
        ·
          refine ⟨18372085982736417557501269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24496114643648556743335025 18372085982736417557501269)
          ·
            refine ⟨1682014707892128072281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 18372085982736417557501269 1682014707892128072281)
            ·
              rfl

theorem cell22_397999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 15].length) (baseStart_397999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_397999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_397999 prefixEnd_397999 := by exact prefixLift 397999
  have htrace : WordTrace (prefixWord ++ tailWord_397999) baseStart_397999 baseEnd_397999 := by
    simpa [prefixWord, tailWord_397999, baseEnd_397999] using wordTrace_append hprefix tailTrace_397999
  have hstable : (prefixWord ++ tailWord_397999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397999).length < 2 ^ (prefixWord ++ tailWord_397999).sum := by decide
  have hdescent : baseEnd_397999 < baseStart_397999 := by decide
  rcases family_descends (prefixWord ++ tailWord_397999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398003 : List Nat := [1, 1, 1, 2, 3, 4, 1, 4, 2, 3]
def baseStart_398003 : Nat := 118140960795 + 398003 * 2 ^ 59
def prefixEnd_398003 : Nat := 4983230072969 + 3 ^ 40 * 398003 * 2
def baseEnd_398003 : Nat := 136244560621007696754749

theorem tailTrace_398003 : CollatzResearch.WordTrace tailWord_398003 prefixEnd_398003 136244560621007696754749 := by
  unfold tailWord_398003
  simp only [CollatzResearch.WordTrace]
  refine ⟨14516361977110579345862663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9677574651407052897241775 14516361977110579345862663)
  ·
    refine ⟨21774542965665869018793995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14516361977110579345862663 21774542965665869018793995)
    ·
      refine ⟨32661814448498803528190993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21774542965665869018793995 32661814448498803528190993)
      ·
        refine ⟨24496360836374102646143245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32661814448498803528190993 24496360836374102646143245)
        ·
          refine ⟨9186135313640288492303717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24496360836374102646143245 9186135313640288492303717)
          ·
            refine ⟨1722400371307554092306947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9186135313640288492303717 1722400371307554092306947)
            ·
              refine ⟨2583600556961331138460421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1722400371307554092306947 2583600556961331138460421)
              ·
                refine ⟨484425104430249588461329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2583600556961331138460421 484425104430249588461329)
                ·
                  refine ⟨363318828322687191345997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484425104430249588461329 363318828322687191345997)
                  ·
                    refine ⟨136244560621007696754749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 363318828322687191345997 136244560621007696754749)
                    ·
                      rfl

theorem cell22_398003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2, 3].length) (baseStart_398003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398003 prefixEnd_398003 := by exact prefixLift 398003
  have htrace : WordTrace (prefixWord ++ tailWord_398003) baseStart_398003 baseEnd_398003 := by
    simpa [prefixWord, tailWord_398003, baseEnd_398003] using wordTrace_append hprefix tailTrace_398003
  have hstable : (prefixWord ++ tailWord_398003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398003).length < 2 ^ (prefixWord ++ tailWord_398003).sum := by decide
  have hdescent : baseEnd_398003 < baseStart_398003 := by decide
  rcases family_descends (prefixWord ++ tailWord_398003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398005 : List Nat := [1, 3, 3, 3, 1, 2, 1, 4, 4]
def baseStart_398005 : Nat := 118140960795 + 398005 * 2 ^ 59
def prefixEnd_398005 : Nat := 4983230072969 + 3 ^ 40 * 398005 * 2
def baseEnd_398005 : Nat := 45415081753960119401581

theorem tailTrace_398005 : CollatzResearch.WordTrace tailWord_398005 prefixEnd_398005 45415081753960119401581 := by
  unfold tailWord_398005
  simp only [CollatzResearch.WordTrace]
  refine ⟨14516434923103333687435469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9677623282068889124956979 14516434923103333687435469)
  ·
    refine ⟨5443663096163750132788301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14516434923103333687435469 5443663096163750132788301)
    ·
      refine ⟨2041373661061406299795613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5443663096163750132788301 2041373661061406299795613)
      ·
        refine ⟨765515122898027362423355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2041373661061406299795613 765515122898027362423355)
        ·
          refine ⟨1148272684347041043635033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 765515122898027362423355 1148272684347041043635033)
          ·
            refine ⟨861204513260280782726275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1148272684347041043635033 861204513260280782726275)
            ·
              refine ⟨1291806769890421174089413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 861204513260280782726275 1291806769890421174089413)
              ·
                refine ⟨242213769354453970141765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1291806769890421174089413 242213769354453970141765)
                ·
                  refine ⟨45415081753960119401581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 242213769354453970141765 45415081753960119401581)
                  ·
                    rfl

theorem cell22_398005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4, 4].length) (baseStart_398005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398005 prefixEnd_398005 := by exact prefixLift 398005
  have htrace : WordTrace (prefixWord ++ tailWord_398005) baseStart_398005 baseEnd_398005 := by
    simpa [prefixWord, tailWord_398005, baseEnd_398005] using wordTrace_append hprefix tailTrace_398005
  have hstable : (prefixWord ++ tailWord_398005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398005).length < 2 ^ (prefixWord ++ tailWord_398005).sum := by decide
  have hdescent : baseEnd_398005 < baseStart_398005 := by decide
  rcases family_descends (prefixWord ++ tailWord_398005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398016 : List Nat := [2, 1, 1, 2, 4, 2, 3, 7]
def baseStart_398016 : Nat := 118140960795 + 398016 * 2 ^ 59
def prefixEnd_398016 : Nat := 4983230072969 + 3 ^ 40 * 398016 * 2
def baseEnd_398016 : Nat := 15138778976297777353301

theorem tailTrace_398016 : CollatzResearch.WordTrace tailWord_398016 prefixEnd_398016 15138778976297777353301 := by
  unfold tailWord_398016
  simp only [CollatzResearch.WordTrace]
  refine ⟨7258418063031741283042951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9677890750708988377390601 7258418063031741283042951)
  ·
    refine ⟨10887627094547611924564427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7258418063031741283042951 10887627094547611924564427)
    ·
      refine ⟨16331440641821417886846641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10887627094547611924564427 16331440641821417886846641)
      ·
        refine ⟨12248580481366063415134981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16331440641821417886846641 12248580481366063415134981)
        ·
          refine ⟨2296608840256136890337809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12248580481366063415134981 2296608840256136890337809)
          ·
            refine ⟨1722456630192102667753357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2296608840256136890337809 1722456630192102667753357)
            ·
              refine ⟨645921236322038500407509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1722456630192102667753357 645921236322038500407509)
              ·
                refine ⟨15138778976297777353301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 645921236322038500407509 15138778976297777353301)
                ·
                  rfl

theorem cell22_398016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 7].length) (baseStart_398016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398016 prefixEnd_398016 := by exact prefixLift 398016
  have htrace : WordTrace (prefixWord ++ tailWord_398016) baseStart_398016 baseEnd_398016 := by
    simpa [prefixWord, tailWord_398016, baseEnd_398016] using wordTrace_append hprefix tailTrace_398016
  have hstable : (prefixWord ++ tailWord_398016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398016).length < 2 ^ (prefixWord ++ tailWord_398016).sum := by decide
  have hdescent : baseEnd_398016 < baseStart_398016 := by decide
  rcases family_descends (prefixWord ++ tailWord_398016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398020 : List Nat := [2, 3, 3, 1, 1, 2, 2, 3, 2, 3]
def baseStart_398020 : Nat := 118140960795 + 398020 * 2 ^ 59
def prefixEnd_398020 : Nat := 4983230072969 + 3 ^ 40 * 398020 * 2
def baseEnd_398020 : Nat := 136250380068425319079697

theorem tailTrace_398020 : CollatzResearch.WordTrace tailWord_398020 prefixEnd_398020 136250380068425319079697 := by
  unfold tailWord_398020
  simp only [CollatzResearch.WordTrace]
  refine ⟨7258491009024495624615757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9677988012032660832821009 7258491009024495624615757)
  ·
    refine ⟨2721934128384185859230909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7258491009024495624615757 2721934128384185859230909)
    ·
      refine ⟨1020725298144069697211591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2721934128384185859230909 1020725298144069697211591)
      ·
        refine ⟨1531087947216104545817387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1020725298144069697211591 1531087947216104545817387)
        ·
          refine ⟨2296631920824156818726081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1531087947216104545817387 2296631920824156818726081)
          ·
            refine ⟨1722473940618117614044561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2296631920824156818726081 1722473940618117614044561)
            ·
              refine ⟨1291855455463588210533421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1722473940618117614044561 1291855455463588210533421)
              ·
                refine ⟨484445795798845578950033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1291855455463588210533421 484445795798845578950033)
                ·
                  refine ⟨363334346849134184212525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484445795798845578950033 363334346849134184212525)
                  ·
                    refine ⟨136250380068425319079697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 363334346849134184212525 136250380068425319079697)
                    ·
                      rfl

theorem cell22_398020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_398020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398020 prefixEnd_398020 := by exact prefixLift 398020
  have htrace : WordTrace (prefixWord ++ tailWord_398020) baseStart_398020 baseEnd_398020 := by
    simpa [prefixWord, tailWord_398020, baseEnd_398020] using wordTrace_append hprefix tailTrace_398020
  have hstable : (prefixWord ++ tailWord_398020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398020).length < 2 ^ (prefixWord ++ tailWord_398020).sum := by decide
  have hdescent : baseEnd_398020 < baseStart_398020 := by decide
  rcases family_descends (prefixWord ++ tailWord_398020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398022 : List Nat := [6, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_398022 : Nat := 118140960795 + 398022 * 2 ^ 59
def prefixEnd_398022 : Nat := 4983230072969 + 3 ^ 40 * 398022 * 2
def baseEnd_398022 : Nat := 45417021569765993509897

theorem tailTrace_398022 : CollatzResearch.WordTrace tailWord_398022 prefixEnd_398022 45417021569765993509897 := by
  unfold tailWord_398022
  simp only [CollatzResearch.WordTrace]
  refine ⟨453657967626304549712635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9678036642694497060536213 453657967626304549712635)
  ·
    refine ⟨680486951439456824568953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 453657967626304549712635 680486951439456824568953)
    ·
      refine ⟨510365213579592618426715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 680486951439456824568953 510365213579592618426715)
      ·
        refine ⟨765547820369388927640073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510365213579592618426715 765547820369388927640073)
        ·
          refine ⟨574160865277041695730055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 765547820369388927640073 574160865277041695730055)
          ·
            refine ⟨861241297915562543595083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574160865277041695730055 861241297915562543595083)
            ·
              refine ⟨1291861946873343815392625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 861241297915562543595083 1291861946873343815392625)
              ·
                refine ⟨968896460155007861544469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1291861946873343815392625 968896460155007861544469)
                ·
                  refine ⟨45417021569765993509897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 968896460155007861544469 45417021569765993509897)
                  ·
                    rfl

theorem cell22_398022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_398022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398022 prefixEnd_398022 := by exact prefixLift 398022
  have htrace : WordTrace (prefixWord ++ tailWord_398022) baseStart_398022 baseEnd_398022 := by
    simpa [prefixWord, tailWord_398022, baseEnd_398022] using wordTrace_append hprefix tailTrace_398022
  have hstable : (prefixWord ++ tailWord_398022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398022).length < 2 ^ (prefixWord ++ tailWord_398022).sum := by decide
  have hdescent : baseEnd_398022 < baseStart_398022 := by decide
  rcases family_descends (prefixWord ++ tailWord_398022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398065 : List Nat := [1, 2, 2, 2, 2, 2, 1, 6, 1, 3]
def baseStart_398065 : Nat := 118140960795 + 398065 * 2 ^ 59
def prefixEnd_398065 : Nat := 4983230072969 + 3 ^ 40 * 398065 * 2
def baseEnd_398065 : Nat := 136265784488060201704559

theorem tailTrace_398065 : CollatzResearch.WordTrace tailWord_398065 prefixEnd_398065 136265784488060201704559 := by
  unfold tailWord_398065
  simp only [CollatzResearch.WordTrace]
  refine ⟨14518623302885963934619649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9679082201923975956413099 14518623302885963934619649)
  ·
    refine ⟨10888967477164472950964737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14518623302885963934619649 10888967477164472950964737)
    ·
      refine ⟨8166725607873354713223553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10888967477164472950964737 8166725607873354713223553)
      ·
        refine ⟨6125044205905016034917665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8166725607873354713223553 6125044205905016034917665)
        ·
          refine ⟨4593783154428762026188249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6125044205905016034917665 4593783154428762026188249)
          ·
            refine ⟨3445337365821571519641187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4593783154428762026188249 3445337365821571519641187)
            ·
              refine ⟨5168006048732357279461781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3445337365821571519641187 5168006048732357279461781)
              ·
                refine ⟨242250283534329247474771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5168006048732357279461781 242250283534329247474771)
                ·
                  refine ⟨363375425301493871212157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 242250283534329247474771 363375425301493871212157)
                  ·
                    refine ⟨136265784488060201704559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 363375425301493871212157 136265784488060201704559)
                    ·
                      rfl

theorem cell22_398065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6, 1, 3].length) (baseStart_398065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398065 prefixEnd_398065 := by exact prefixLift 398065
  have htrace : WordTrace (prefixWord ++ tailWord_398065) baseStart_398065 baseEnd_398065 := by
    simpa [prefixWord, tailWord_398065, baseEnd_398065] using wordTrace_append hprefix tailTrace_398065
  have hstable : (prefixWord ++ tailWord_398065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398065).length < 2 ^ (prefixWord ++ tailWord_398065).sum := by decide
  have hdescent : baseEnd_398065 < baseStart_398065 := by decide
  rcases family_descends (prefixWord ++ tailWord_398065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398121 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 3, 5]
def baseStart_398121 : Nat := 118140960795 + 398121 * 2 ^ 59
def prefixEnd_398121 : Nat := 4983230072969 + 3 ^ 40 * 398121 * 2
def baseEnd_398121 : Nat := 136284954432494722304387

theorem tailTrace_398121 : CollatzResearch.WordTrace tailWord_398121 prefixEnd_398121 136284954432494722304387 := by
  unfold tailWord_398121
  simp only [CollatzResearch.WordTrace]
  refine ⟨14520665790683085498658217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9680443860455390332438811 14520665790683085498658217)
  ·
    refine ⟨10890499343012314123993663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14520665790683085498658217 10890499343012314123993663)
    ·
      refine ⟨16335749014518471185990495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10890499343012314123993663 16335749014518471185990495)
      ·
        refine ⟨24503623521777706778985743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16335749014518471185990495 24503623521777706778985743)
        ·
          refine ⟨36755435282666560168478615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24503623521777706778985743 36755435282666560168478615)
          ·
            refine ⟨55133152923999840252717923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36755435282666560168478615 55133152923999840252717923)
            ·
              refine ⟨82699729385999760379076885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55133152923999840252717923 82699729385999760379076885)
              ·
                refine ⟨3876549814968738767769229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82699729385999760379076885 3876549814968738767769229)
                ·
                  refine ⟨1453706180613277037913461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3876549814968738767769229 1453706180613277037913461)
                  ·
                    refine ⟨136284954432494722304387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1453706180613277037913461 136284954432494722304387)
                    ·
                      rfl

theorem cell22_398121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 5].length) (baseStart_398121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398121 prefixEnd_398121 := by exact prefixLift 398121
  have htrace : WordTrace (prefixWord ++ tailWord_398121) baseStart_398121 baseEnd_398121 := by
    simpa [prefixWord, tailWord_398121, baseEnd_398121] using wordTrace_append hprefix tailTrace_398121
  have hstable : (prefixWord ++ tailWord_398121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398121).length < 2 ^ (prefixWord ++ tailWord_398121).sum := by decide
  have hdescent : baseEnd_398121 < baseStart_398121 := by decide
  rcases family_descends (prefixWord ++ tailWord_398121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398153 : List Nat := [1, 2, 1, 1, 2, 5, 1, 3, 2, 4]
def baseStart_398153 : Nat := 118140960795 + 398153 * 2 ^ 59
def prefixEnd_398153 : Nat := 4983230072969 + 3 ^ 40 * 398153 * 2
def baseEnd_398153 : Nat := 136295908686457305504289

theorem tailTrace_398153 : CollatzResearch.WordTrace tailWord_398153 prefixEnd_398153 136295908686457305504289 := by
  unfold tailWord_398153
  simp only [CollatzResearch.WordTrace]
  refine ⟨14521832926567154963823113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9681221951044769975882075 14521832926567154963823113)
  ·
    refine ⟨10891374694925366222867335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14521832926567154963823113 10891374694925366222867335)
    ·
      refine ⟨16337062042388049334301003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10891374694925366222867335 16337062042388049334301003)
      ·
        refine ⟨24505593063582074001451505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16337062042388049334301003 24505593063582074001451505)
        ·
          refine ⟨18379194797686555501088629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24505593063582074001451505 18379194797686555501088629)
          ·
            refine ⟨1723049512283114578227059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18379194797686555501088629 1723049512283114578227059)
            ·
              refine ⟨2584574268424671867340589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1723049512283114578227059 2584574268424671867340589)
              ·
                refine ⟨969215350659251950252721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2584574268424671867340589 969215350659251950252721)
                ·
                  refine ⟨726911512994438962689541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 969215350659251950252721 726911512994438962689541)
                  ·
                    refine ⟨136295908686457305504289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 726911512994438962689541 136295908686457305504289)
                    ·
                      rfl

theorem cell22_398153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 4].length) (baseStart_398153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398153 prefixEnd_398153 := by exact prefixLift 398153
  have htrace : WordTrace (prefixWord ++ tailWord_398153) baseStart_398153 baseEnd_398153 := by
    simpa [prefixWord, tailWord_398153, baseEnd_398153] using wordTrace_append hprefix tailTrace_398153
  have hstable : (prefixWord ++ tailWord_398153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398153).length < 2 ^ (prefixWord ++ tailWord_398153).sum := by decide
  have hdescent : baseEnd_398153 < baseStart_398153 := by decide
  rcases family_descends (prefixWord ++ tailWord_398153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398172 : List Nat := [2, 2, 4, 2, 1, 1, 1, 4, 2, 3]
def baseStart_398172 : Nat := 118140960795 + 398172 * 2 ^ 59
def prefixEnd_398172 : Nat := 4983230072969 + 3 ^ 40 * 398172 * 2
def baseEnd_398172 : Nat := 136302412774747589279231

theorem tailTrace_398172 : CollatzResearch.WordTrace tailWord_398172 prefixEnd_398172 136302412774747589279231 := by
  unfold tailWord_398172
  simp only [CollatzResearch.WordTrace]
  refine ⟨7261262956749160604382385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9681683942332214139176513 7261262956749160604382385)
  ·
    refine ⟨5445947217561870453286789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7261262956749160604382385 5445947217561870453286789)
    ·
      refine ⟨1021115103292850709991273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5445947217561870453286789 1021115103292850709991273)
      ·
        refine ⟨765836327469638032493455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1021115103292850709991273 765836327469638032493455)
        ·
          refine ⟨1148754491204457048740183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 765836327469638032493455 1148754491204457048740183)
          ·
            refine ⟨1723131736806685573110275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148754491204457048740183 1723131736806685573110275)
            ·
              refine ⟨2584697605210028359665413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1723131736806685573110275 2584697605210028359665413)
              ·
                refine ⟨484630800976880317437265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2584697605210028359665413 484630800976880317437265)
                ·
                  refine ⟨363473100732660238077949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484630800976880317437265 363473100732660238077949)
                  ·
                    refine ⟨136302412774747589279231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 363473100732660238077949 136302412774747589279231)
                    ·
                      rfl

theorem cell22_398172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_398172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398172 prefixEnd_398172 := by exact prefixLift 398172
  have htrace : WordTrace (prefixWord ++ tailWord_398172) baseStart_398172 baseEnd_398172 := by
    simpa [prefixWord, tailWord_398172, baseEnd_398172] using wordTrace_append hprefix tailTrace_398172
  have hstable : (prefixWord ++ tailWord_398172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398172).length < 2 ^ (prefixWord ++ tailWord_398172).sum := by decide
  have hdescent : baseEnd_398172 < baseStart_398172 := by decide
  rcases family_descends (prefixWord ++ tailWord_398172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398217 : List Nat := [1, 2, 1, 1, 5, 2, 1, 5, 1, 3]
def baseStart_398217 : Nat := 118140960795 + 398217 * 2 ^ 59
def prefixEnd_398217 : Nat := 4983230072969 + 3 ^ 40 * 398217 * 2
def baseEnd_398217 : Nat := 136317817194382471904093

theorem tailTrace_398217 : CollatzResearch.WordTrace tailWord_398217 prefixEnd_398217 136317817194382471904093 := by
  unfold tailWord_398217
  simp only [CollatzResearch.WordTrace]
  refine ⟨14524167198335293894152905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9682778132223529262768603 14524167198335293894152905)
  ·
    refine ⟨10893125398751470420614679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14524167198335293894152905 10893125398751470420614679)
    ·
      refine ⟨16339688098127205630922019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10893125398751470420614679 16339688098127205630922019)
      ·
        refine ⟨24509532147190808446383029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16339688098127205630922019 24509532147190808446383029)
        ·
          refine ⟨2297768638799138291848409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24509532147190808446383029 2297768638799138291848409)
          ·
            refine ⟨1723326479099353718886307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2297768638799138291848409 1723326479099353718886307)
            ·
              refine ⟨2584989718649030578329461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1723326479099353718886307 2584989718649030578329461)
              ·
                refine ⟨242342786123346616718387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2584989718649030578329461 242342786123346616718387)
                ·
                  refine ⟨363514179185019925077581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 242342786123346616718387 363514179185019925077581)
                  ·
                    refine ⟨136317817194382471904093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 363514179185019925077581 136317817194382471904093)
                    ·
                      rfl

theorem cell22_398217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5, 1, 3].length) (baseStart_398217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398217 prefixEnd_398217 := by exact prefixLift 398217
  have htrace : WordTrace (prefixWord ++ tailWord_398217) baseStart_398217 baseEnd_398217 := by
    simpa [prefixWord, tailWord_398217, baseEnd_398217] using wordTrace_append hprefix tailTrace_398217
  have hstable : (prefixWord ++ tailWord_398217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398217).length < 2 ^ (prefixWord ++ tailWord_398217).sum := by decide
  have hdescent : baseEnd_398217 < baseStart_398217 := by decide
  rcases family_descends (prefixWord ++ tailWord_398217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398243 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 5, 4]
def baseStart_398243 : Nat := 118140960795 + 398243 * 2 ^ 59
def prefixEnd_398243 : Nat := 4983230072969 + 3 ^ 40 * 398243 * 2
def baseEnd_398243 : Nat := 136326717525727070754013

theorem tailTrace_398243 : CollatzResearch.WordTrace tailWord_398243 prefixEnd_398243 136326717525727070754013 := by
  unfold tailWord_398243
  simp only [CollatzResearch.WordTrace]
  refine ⟨14525115496241100334599383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9683410330827400223066255 14525115496241100334599383)
  ·
    refine ⟨21787673244361650501899075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14525115496241100334599383 21787673244361650501899075)
    ·
      refine ⟨32681509866542475752848613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21787673244361650501899075 32681509866542475752848613)
      ·
        refine ⟨6127783099976714203659115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32681509866542475752848613 6127783099976714203659115)
        ·
          refine ⟨9191674649965071305488673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6127783099976714203659115 9191674649965071305488673)
          ·
            refine ⟨6893755987473803479116505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9191674649965071305488673 6893755987473803479116505)
            ·
              refine ⟨5170316990605352609337379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6893755987473803479116505 5170316990605352609337379)
              ·
                refine ⟨7755475485908028914006069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5170316990605352609337379 7755475485908028914006069)
                ·
                  refine ⟨727075826803877710688069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7755475485908028914006069 727075826803877710688069)
                  ·
                    refine ⟨136326717525727070754013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 727075826803877710688069 136326717525727070754013)
                    ·
                      rfl

theorem cell22_398243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 4].length) (baseStart_398243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398243 prefixEnd_398243 := by exact prefixLift 398243
  have htrace : WordTrace (prefixWord ++ tailWord_398243) baseStart_398243 baseEnd_398243 := by
    simpa [prefixWord, tailWord_398243, baseEnd_398243] using wordTrace_append hprefix tailTrace_398243
  have hstable : (prefixWord ++ tailWord_398243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398243).length < 2 ^ (prefixWord ++ tailWord_398243).sum := by decide
  have hdescent : baseEnd_398243 < baseStart_398243 := by decide
  rcases family_descends (prefixWord ++ tailWord_398243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398285 : List Nat := [1, 6, 3, 1, 2, 1, 1, 1, 3, 3]
def baseStart_398285 : Nat := 118140960795 + 398285 * 2 ^ 59
def prefixEnd_398285 : Nat := 4983230072969 + 3 ^ 40 * 398285 * 2
def baseEnd_398285 : Nat := 136341094984052961203885

theorem tailTrace_398285 : CollatzResearch.WordTrace tailWord_398285 prefixEnd_398285 136341094984052961203885 := by
  unfold tailWord_398285
  simp only [CollatzResearch.WordTrace]
  refine ⟨14526647362088941507628309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9684431574725961005085539 14526647362088941507628309)
  ·
    refine ⟨680936595097919133170077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14526647362088941507628309 680936595097919133170077)
    ·
      refine ⟨255351223161719674938779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 680936595097919133170077 255351223161719674938779)
      ·
        refine ⟨383026834742579512408169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255351223161719674938779 383026834742579512408169)
        ·
          refine ⟨287270126056934634306127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383026834742579512408169 287270126056934634306127)
          ·
            refine ⟨430905189085401951459191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287270126056934634306127 430905189085401951459191)
            ·
              refine ⟨646357783628102927188787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430905189085401951459191 646357783628102927188787)
              ·
                refine ⟨969536675442154390783181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 646357783628102927188787 969536675442154390783181)
                ·
                  refine ⟨363576253290807896543693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 969536675442154390783181 363576253290807896543693)
                  ·
                    refine ⟨136341094984052961203885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 363576253290807896543693 136341094984052961203885)
                    ·
                      rfl

theorem cell22_398285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_398285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398285 prefixEnd_398285 := by exact prefixLift 398285
  have htrace : WordTrace (prefixWord ++ tailWord_398285) baseStart_398285 baseEnd_398285 := by
    simpa [prefixWord, tailWord_398285, baseEnd_398285] using wordTrace_append hprefix tailTrace_398285
  have hstable : (prefixWord ++ tailWord_398285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398285).length < 2 ^ (prefixWord ++ tailWord_398285).sum := by decide
  have hdescent : baseEnd_398285 < baseStart_398285 := by decide
  rcases family_descends (prefixWord ++ tailWord_398285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398292 : List Nat := [2, 4, 1, 2, 1, 4, 1, 1, 6]
def baseStart_398292 : Nat := 118140960795 + 398292 * 2 ^ 59
def prefixEnd_398292 : Nat := 4983230072969 + 3 ^ 40 * 398292 * 2
def baseEnd_398292 : Nat := 45447830409035758759621

theorem tailTrace_398292 : CollatzResearch.WordTrace tailWord_398292 prefixEnd_398292 45447830409035758759621 := by
  unfold tailWord_398292
  simp only [CollatzResearch.WordTrace]
  refine ⟨7263451336531790851566565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9684601782042387802088753 7263451336531790851566565)
  ·
    refine ⟨1361897125599710784668731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7263451336531790851566565 1361897125599710784668731)
    ·
      refine ⟨2042845688399566177003097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1361897125599710784668731 2042845688399566177003097)
      ·
        refine ⟨1532134266299674632752323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2042845688399566177003097 1532134266299674632752323)
        ·
          refine ⟨2298201399449511949128485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1532134266299674632752323 2298201399449511949128485)
          ·
            refine ⟨430912762396783490461591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2298201399449511949128485 430912762396783490461591)
            ·
              refine ⟨646369143595175235692387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430912762396783490461591 646369143595175235692387)
              ·
                refine ⟨969553715392762853538581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 646369143595175235692387 969553715392762853538581)
                ·
                  refine ⟨45447830409035758759621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 969553715392762853538581 45447830409035758759621)
                  ·
                    rfl

theorem cell22_398292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_398292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398292 prefixEnd_398292 := by exact prefixLift 398292
  have htrace : WordTrace (prefixWord ++ tailWord_398292) baseStart_398292 baseEnd_398292 := by
    simpa [prefixWord, tailWord_398292, baseEnd_398292] using wordTrace_append hprefix tailTrace_398292
  have hstable : (prefixWord ++ tailWord_398292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398292).length < 2 ^ (prefixWord ++ tailWord_398292).sum := by decide
  have hdescent : baseEnd_398292 < baseStart_398292 := by decide
  rcases family_descends (prefixWord ++ tailWord_398292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398307 : List Nat := [1, 1, 1, 6, 1, 1, 3, 3, 2, 3]
def baseStart_398307 : Nat := 118140960795 + 398307 * 2 ^ 59
def prefixEnd_398307 : Nat := 4983230072969 + 3 ^ 40 * 398307 * 2
def baseEnd_398307 : Nat := 136348626033652237153817

theorem tailTrace_398307 : CollatzResearch.WordTrace tailWord_398307 prefixEnd_398307 136348626033652237153817 := by
  unfold tailWord_398307
  simp only [CollatzResearch.WordTrace]
  refine ⟨14527449768009239264929175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9684966512006159509952783 14527449768009239264929175)
  ·
    refine ⟨21791174652013858897393763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14527449768009239264929175 21791174652013858897393763)
    ·
      refine ⟨32686761978020788346090645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21791174652013858897393763 32686761978020788346090645)
      ·
        refine ⟨1532191967719724453722999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32686761978020788346090645 1532191967719724453722999)
        ·
          refine ⟨2298287951579586680584499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1532191967719724453722999 2298287951579586680584499)
          ·
            refine ⟨3447431927369380020876749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2298287951579586680584499 3447431927369380020876749)
            ·
              refine ⟨1292786972763517507828781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3447431927369380020876749 1292786972763517507828781)
              ·
                refine ⟨484795114786319065435793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1292786972763517507828781 484795114786319065435793)
                ·
                  refine ⟨363596336089739299076845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484795114786319065435793 363596336089739299076845)
                  ·
                    refine ⟨136348626033652237153817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 363596336089739299076845 136348626033652237153817)
                    ·
                      rfl

theorem cell22_398307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2, 3].length) (baseStart_398307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398307 prefixEnd_398307 := by exact prefixLift 398307
  have htrace : WordTrace (prefixWord ++ tailWord_398307) baseStart_398307 baseEnd_398307 := by
    simpa [prefixWord, tailWord_398307, baseEnd_398307] using wordTrace_append hprefix tailTrace_398307
  have hstable : (prefixWord ++ tailWord_398307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398307).length < 2 ^ (prefixWord ++ tailWord_398307).sum := by decide
  have hdescent : baseEnd_398307 < baseStart_398307 := by decide
  rcases family_descends (prefixWord ++ tailWord_398307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398350 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 2, 6]
def baseStart_398350 : Nat := 118140960795 + 398350 * 2 ^ 59
def prefixEnd_398350 : Nat := 4983230072969 + 3 ^ 40 * 398350 * 2
def baseEnd_398350 : Nat := 136363345812414458328685

theorem tailTrace_398350 : CollatzResearch.WordTrace tailWord_398350 prefixEnd_398350 136363345812414458328685 := by
  unfold tailWord_398350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1816127263356682201093063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9686012071235638405829669 1816127263356682201093063)
  ·
    refine ⟨2724190895035023301639595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1816127263356682201093063 2724190895035023301639595)
    ·
      refine ⟨4086286342552534952459393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2724190895035023301639595 4086286342552534952459393)
      ·
        refine ⟨3064714756914401214344545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4086286342552534952459393 3064714756914401214344545)
        ·
          refine ⟨2298536067685800910758409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3064714756914401214344545 2298536067685800910758409)
          ·
            refine ⟨1723902050764350683068807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2298536067685800910758409 1723902050764350683068807)
            ·
              refine ⟨2585853076146526024603211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1723902050764350683068807 2585853076146526024603211)
              ·
                refine ⟨3878779614219789036904817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2585853076146526024603211 3878779614219789036904817)
                ·
                  refine ⟨2909084710664841777678613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3878779614219789036904817 2909084710664841777678613)
                  ·
                    refine ⟨136363345812414458328685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2909084710664841777678613 136363345812414458328685)
                    ·
                      rfl

theorem cell22_398350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_398350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398350 prefixEnd_398350 := by exact prefixLift 398350
  have htrace : WordTrace (prefixWord ++ tailWord_398350) baseStart_398350 baseEnd_398350 := by
    simpa [prefixWord, tailWord_398350, baseEnd_398350] using wordTrace_append hprefix tailTrace_398350
  have hstable : (prefixWord ++ tailWord_398350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398350).length < 2 ^ (prefixWord ++ tailWord_398350).sum := by decide
  have hdescent : baseEnd_398350 < baseStart_398350 := by decide
  rcases family_descends (prefixWord ++ tailWord_398350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398410 : List Nat := [3, 1, 2, 1, 1, 2, 3, 3, 6]
def baseStart_398410 : Nat := 118140960795 + 398410 * 2 ^ 59
def prefixEnd_398410 : Nat := 4983230072969 + 3 ^ 40 * 398410 * 2
def baseEnd_398410 : Nat := 45461295012864767276167

theorem tailTrace_398410 : CollatzResearch.WordTrace tailWord_398410 prefixEnd_398410 45461295012864767276167 := by
  unfold tailWord_398410
  simp only [CollatzResearch.WordTrace]
  refine ⟨3632801621659021963982171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9687470991090725237285789 3632801621659021963982171)
  ·
    refine ⟨5449202432488532945973257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3632801621659021963982171 5449202432488532945973257)
    ·
      refine ⟨4086901824366399709479943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5449202432488532945973257 4086901824366399709479943)
      ·
        refine ⟨6130352736549599564219915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4086901824366399709479943 6130352736549599564219915)
        ·
          refine ⟨9195529104824399346329873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6130352736549599564219915 9195529104824399346329873)
          ·
            refine ⟨6896646828618299509747405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9195529104824399346329873 6896646828618299509747405)
            ·
              refine ⟨2586242560731862316155277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6896646828618299509747405 2586242560731862316155277)
              ·
                refine ⟨969840960274448368558229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2586242560731862316155277 969840960274448368558229)
                ·
                  refine ⟨45461295012864767276167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 969840960274448368558229 45461295012864767276167)
                  ·
                    rfl

theorem cell22_398410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 6].length) (baseStart_398410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398410 prefixEnd_398410 := by exact prefixLift 398410
  have htrace : WordTrace (prefixWord ++ tailWord_398410) baseStart_398410 baseEnd_398410 := by
    simpa [prefixWord, tailWord_398410, baseEnd_398410] using wordTrace_append hprefix tailTrace_398410
  have hstable : (prefixWord ++ tailWord_398410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398410).length < 2 ^ (prefixWord ++ tailWord_398410).sum := by decide
  have hdescent : baseEnd_398410 < baseStart_398410 := by decide
  rcases family_descends (prefixWord ++ tailWord_398410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398425 : List Nat := [1, 2, 1, 2, 2, 1, 2, 5, 1, 5]
def baseStart_398425 : Nat := 118140960795 + 398425 * 2 ^ 59
def prefixEnd_398425 : Nat := 4983230072969 + 3 ^ 40 * 398425 * 2
def baseEnd_398425 : Nat := 136389019845139262703455

theorem tailTrace_398425 : CollatzResearch.WordTrace tailWord_398425 prefixEnd_398425 136389019845139262703455 := by
  unfold tailWord_398425
  simp only [CollatzResearch.WordTrace]
  refine ⟨14531753581581745417724729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9687835721054496945149819 14531753581581745417724729)
  ·
    refine ⟨10898815186186309063293547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14531753581581745417724729 10898815186186309063293547)
    ·
      refine ⟨16348222779279463594940321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10898815186186309063293547 16348222779279463594940321)
      ·
        refine ⟨12261167084459597696205241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16348222779279463594940321 12261167084459597696205241)
        ·
          refine ⟨9195875313344698272153931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12261167084459597696205241 9195875313344698272153931)
          ·
            refine ⟨13793812970017047408230897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9195875313344698272153931 13793812970017047408230897)
            ·
              refine ⟨10345359727512785556173173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13793812970017047408230897 10345359727512785556173173)
              ·
                refine ⟨969877474454323645891235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10345359727512785556173173 969877474454323645891235)
                ·
                  refine ⟨1454816211681485468836853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 969877474454323645891235 1454816211681485468836853)
                  ·
                    refine ⟨136389019845139262703455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1454816211681485468836853 136389019845139262703455)
                    ·
                      rfl

theorem cell22_398425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 5].length) (baseStart_398425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398425 prefixEnd_398425 := by exact prefixLift 398425
  have htrace : WordTrace (prefixWord ++ tailWord_398425) baseStart_398425 baseEnd_398425 := by
    simpa [prefixWord, tailWord_398425, baseEnd_398425] using wordTrace_append hprefix tailTrace_398425
  have hstable : (prefixWord ++ tailWord_398425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398425).length < 2 ^ (prefixWord ++ tailWord_398425).sum := by decide
  have hdescent : baseEnd_398425 < baseStart_398425 := by decide
  rcases family_descends (prefixWord ++ tailWord_398425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398485 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 4, 6]
def baseStart_398485 : Nat := 118140960795 + 398485 * 2 ^ 59
def prefixEnd_398485 : Nat := 4983230072969 + 3 ^ 40 * 398485 * 2
def baseEnd_398485 : Nat := 136409559071319106203271

theorem tailTrace_398485 : CollatzResearch.WordTrace tailWord_398485 prefixEnd_398485 136409559071319106203271 := by
  unfold tailWord_398485
  simp only [CollatzResearch.WordTrace]
  refine ⟨14533941961364375664908909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9689294640909583776605939 14533941961364375664908909)
  ·
    refine ⟨5450228235511640874340841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14533941961364375664908909 5450228235511640874340841)
    ·
      refine ⟨4087671176633730655755631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5450228235511640874340841 4087671176633730655755631)
      ·
        refine ⟨6131506764950595983633447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4087671176633730655755631 6131506764950595983633447)
        ·
          refine ⟨9197260147425893975450171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6131506764950595983633447 9197260147425893975450171)
          ·
            refine ⟨13795890221138840963175257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9197260147425893975450171 13795890221138840963175257)
            ·
              refine ⟨10346917665854130722381443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13795890221138840963175257 10346917665854130722381443)
              ·
                refine ⟨15520376498781196083572165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10346917665854130722381443 15520376498781196083572165)
                ·
                  refine ⟨2910070593521474265669781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15520376498781196083572165 2910070593521474265669781)
                  ·
                    refine ⟨136409559071319106203271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2910070593521474265669781 136409559071319106203271)
                    ·
                      rfl

theorem cell22_398485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_398485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398485 prefixEnd_398485 := by exact prefixLift 398485
  have htrace : WordTrace (prefixWord ++ tailWord_398485) baseStart_398485 baseEnd_398485 := by
    simpa [prefixWord, tailWord_398485, baseEnd_398485] using wordTrace_append hprefix tailTrace_398485
  have hstable : (prefixWord ++ tailWord_398485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398485).length < 2 ^ (prefixWord ++ tailWord_398485).sum := by decide
  have hdescent : baseEnd_398485 < baseStart_398485 := by decide
  rcases family_descends (prefixWord ++ tailWord_398485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398521 : List Nat := [1, 2, 1, 4, 1, 4, 1, 4, 1, 3]
def baseStart_398521 : Nat := 118140960795 + 398521 * 2 ^ 59
def prefixEnd_398521 : Nat := 4983230072969 + 3 ^ 40 * 398521 * 2
def baseEnd_398521 : Nat := 136421882607027012303161

theorem tailTrace_398521 : CollatzResearch.WordTrace tailWord_398521 prefixEnd_398521 136421882607027012303161 := by
  unfold tailWord_398521
  simp only [CollatzResearch.WordTrace]
  refine ⟨14535254989233953813219417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9690169992822635875479611 14535254989233953813219417)
  ·
    refine ⟨10901441241925465359914563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14535254989233953813219417 10901441241925465359914563)
    ·
      refine ⟨16352161862888198039871845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10901441241925465359914563 16352161862888198039871845)
      ·
        refine ⟨3066030349291537132475971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16352161862888198039871845 3066030349291537132475971)
        ·
          refine ⟨4599045523937305698713957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3066030349291537132475971 4599045523937305698713957)
          ·
            refine ⟨862321035738244818508867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4599045523937305698713957 862321035738244818508867)
            ·
              refine ⟨1293481553607367227763301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 862321035738244818508867 1293481553607367227763301)
              ·
                refine ⟨242527791301381355205619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1293481553607367227763301 242527791301381355205619)
                ·
                  refine ⟨363791686952072032808429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 242527791301381355205619 363791686952072032808429)
                  ·
                    refine ⟨136421882607027012303161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 363791686952072032808429 136421882607027012303161)
                    ·
                      rfl

theorem cell22_398521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4, 1, 3].length) (baseStart_398521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398521 prefixEnd_398521 := by exact prefixLift 398521
  have htrace : WordTrace (prefixWord ++ tailWord_398521) baseStart_398521 baseEnd_398521 := by
    simpa [prefixWord, tailWord_398521, baseEnd_398521] using wordTrace_append hprefix tailTrace_398521
  have hstable : (prefixWord ++ tailWord_398521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398521).length < 2 ^ (prefixWord ++ tailWord_398521).sum := by decide
  have hdescent : baseEnd_398521 < baseStart_398521 := by decide
  rcases family_descends (prefixWord ++ tailWord_398521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398579 : List Nat := [1, 1, 1, 2, 2, 5, 2, 4, 4]
def baseStart_398579 : Nat := 118140960795 + 398579 * 2 ^ 59
def prefixEnd_398579 : Nat := 4983230072969 + 3 ^ 40 * 398579 * 2
def baseEnd_398579 : Nat := 45480579064111398117661

theorem tailTrace_398579 : CollatzResearch.WordTrace tailWord_398579 prefixEnd_398579 45480579064111398117661 := by
  unfold tailWord_398579
  simp only [CollatzResearch.WordTrace]
  refine ⟨14537370423023829718830791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9691580282015886479220527 14537370423023829718830791)
  ·
    refine ⟨21806055634535744578246187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14537370423023829718830791 21806055634535744578246187)
    ·
      refine ⟨32709083451803616867369281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21806055634535744578246187 32709083451803616867369281)
      ·
        refine ⟨24531812588852712650526961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32709083451803616867369281 24531812588852712650526961)
        ·
          refine ⟨18398859441639534487895221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24531812588852712650526961 18398859441639534487895221)
          ·
            refine ⟨1724893072653706358240177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18398859441639534487895221 1724893072653706358240177)
            ·
              refine ⟨1293669804490279768680133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1724893072653706358240177 1293669804490279768680133)
              ·
                refine ⟨242563088341927456627525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1293669804490279768680133 242563088341927456627525)
                ·
                  refine ⟨45480579064111398117661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 242563088341927456627525 45480579064111398117661)
                  ·
                    rfl

theorem cell22_398579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4, 4].length) (baseStart_398579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398579 prefixEnd_398579 := by exact prefixLift 398579
  have htrace : WordTrace (prefixWord ++ tailWord_398579) baseStart_398579 baseEnd_398579 := by
    simpa [prefixWord, tailWord_398579, baseEnd_398579] using wordTrace_append hprefix tailTrace_398579
  have hstable : (prefixWord ++ tailWord_398579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398579).length < 2 ^ (prefixWord ++ tailWord_398579).sum := by decide
  have hdescent : baseEnd_398579 < baseStart_398579 := by decide
  rcases family_descends (prefixWord ++ tailWord_398579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398624 : List Nat := [2, 1, 1, 5, 3, 2, 8]
def baseStart_398624 : Nat := 118140960795 + 398624 * 2 ^ 59
def prefixEnd_398624 : Nat := 4983230072969 + 3 ^ 40 * 398624 * 2
def baseEnd_398624 : Nat := 5053968207850706554735

theorem tailTrace_398624 : CollatzResearch.WordTrace tailWord_398624 prefixEnd_398624 5053968207850706554735 := by
  unfold tailWord_398624
  simp only [CollatzResearch.WordTrace]
  refine ⟨7269505853930401202109463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9692674471907201602812617 7269505853930401202109463)
  ·
    refine ⟨10904258780895601803164195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7269505853930401202109463 10904258780895601803164195)
    ·
      refine ⟨16356388171343402704746293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10904258780895601803164195 16356388171343402704746293)
      ·
        refine ⟨1533411391063444003569965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16356388171343402704746293 1533411391063444003569965)
        ·
          refine ⟨575029271648791501338737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1533411391063444003569965 575029271648791501338737)
          ·
            refine ⟨431271953736593626004053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 575029271648791501338737 431271953736593626004053)
            ·
              refine ⟨5053968207850706554735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 431271953736593626004053 5053968207850706554735)
              ·
                rfl

theorem cell22_398624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 8].length) (baseStart_398624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398624 prefixEnd_398624 := by exact prefixLift 398624
  have htrace : WordTrace (prefixWord ++ tailWord_398624) baseStart_398624 baseEnd_398624 := by
    simpa [prefixWord, tailWord_398624, baseEnd_398624] using wordTrace_append hprefix tailTrace_398624
  have hstable : (prefixWord ++ tailWord_398624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398624).length < 2 ^ (prefixWord ++ tailWord_398624).sum := by decide
  have hdescent : baseEnd_398624 < baseStart_398624 := by decide
  rcases family_descends (prefixWord ++ tailWord_398624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398626 : List Nat := [3, 3, 1, 1, 4, 1, 1, 2, 2, 4]
def baseStart_398626 : Nat := 118140960795 + 398626 * 2 ^ 59
def prefixEnd_398626 : Nat := 4983230072969 + 3 ^ 40 * 398626 * 2
def baseEnd_398626 : Nat := 136457826252841738427839

theorem tailTrace_398626 : CollatzResearch.WordTrace tailWord_398626 prefixEnd_398626 136457826252841738427839 := by
  unfold tailWord_398626
  simp only [CollatzResearch.WordTrace]
  refine ⟨3634771163463389186447933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9692723102569037830527821 3634771163463389186447933)
  ·
    refine ⟨1363039186298770944917975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3634771163463389186447933 1363039186298770944917975)
    ·
      refine ⟨2044558779448156417376963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1363039186298770944917975 2044558779448156417376963)
      ·
        refine ⟨3066838169172234626065445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2044558779448156417376963 3066838169172234626065445)
        ·
          refine ⟨575032156719793992387271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3066838169172234626065445 575032156719793992387271)
          ·
            refine ⟨862548235079690988580907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575032156719793992387271 862548235079690988580907)
            ·
              refine ⟨1293822352619536482871361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 862548235079690988580907 1293822352619536482871361)
              ·
                refine ⟨970366764464652362153521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1293822352619536482871361 970366764464652362153521)
                ·
                  refine ⟨727775073348489271615141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 970366764464652362153521 727775073348489271615141)
                  ·
                    refine ⟨136457826252841738427839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 727775073348489271615141 136457826252841738427839)
                    ·
                      rfl

theorem cell22_398626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_398626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398626 prefixEnd_398626 := by exact prefixLift 398626
  have htrace : WordTrace (prefixWord ++ tailWord_398626) baseStart_398626 baseEnd_398626 := by
    simpa [prefixWord, tailWord_398626, baseEnd_398626] using wordTrace_append hprefix tailTrace_398626
  have hstable : (prefixWord ++ tailWord_398626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398626).length < 2 ^ (prefixWord ++ tailWord_398626).sum := by decide
  have hdescent : baseEnd_398626 < baseStart_398626 := by decide
  rcases family_descends (prefixWord ++ tailWord_398626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398731 : List Nat := [1, 1, 1, 1, 4, 3, 4, 3, 4]
def baseStart_398731 : Nat := 118140960795 + 398731 * 2 ^ 59
def prefixEnd_398731 : Nat := 4983230072969 + 3 ^ 40 * 398731 * 2
def baseEnd_398731 : Nat := 45497923299552154850839

theorem tailTrace_398731 : CollatzResearch.WordTrace tailWord_398731 prefixEnd_398731 45497923299552154850839 := by
  unfold tailWord_398731
  simp only [CollatzResearch.WordTrace]
  refine ⟨14542914318473159678364047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9695276212315439785576031 14542914318473159678364047)
  ·
    refine ⟨21814371477709739517546071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14542914318473159678364047 21814371477709739517546071)
    ·
      refine ⟨32721557216564609276319107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21814371477709739517546071 32721557216564609276319107)
      ·
        refine ⟨49082335824846913914478661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32721557216564609276319107 49082335824846913914478661)
        ·
          refine ⟨9202937967158796358964749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49082335824846913914478661 9202937967158796358964749)
          ·
            refine ⟨3451101737684548634611781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9202937967158796358964749 3451101737684548634611781)
            ·
              refine ⟨647081575815852868989709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3451101737684548634611781 647081575815852868989709)
              ·
                refine ⟨242655590930944825871141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 647081575815852868989709 242655590930944825871141)
                ·
                  refine ⟨45497923299552154850839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 242655590930944825871141 45497923299552154850839)
                  ·
                    rfl

theorem cell22_398731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3, 4].length) (baseStart_398731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398731 prefixEnd_398731 := by exact prefixLift 398731
  have htrace : WordTrace (prefixWord ++ tailWord_398731) baseStart_398731 baseEnd_398731 := by
    simpa [prefixWord, tailWord_398731, baseEnd_398731] using wordTrace_append hprefix tailTrace_398731
  have hstable : (prefixWord ++ tailWord_398731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398731).length < 2 ^ (prefixWord ++ tailWord_398731).sum := by decide
  have hdescent : baseEnd_398731 < baseStart_398731 := by decide
  rcases family_descends (prefixWord ++ tailWord_398731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398746 : List Nat := [3, 1, 1, 4, 1, 1, 3, 1, 4, 3]
def baseStart_398746 : Nat := 118140960795 + 398746 * 2 ^ 59
def prefixEnd_398746 : Nat := 4983230072969 + 3 ^ 40 * 398746 * 2
def baseEnd_398746 : Nat := 136498904705201425427471

theorem tailTrace_398746 : CollatzResearch.WordTrace tailWord_398746 prefixEnd_398746 136498904705201425427471 := by
  unfold tailWord_398746
  simp only [CollatzResearch.WordTrace]
  refine ⟨3635865353354704310040023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9695640942279211493440061 3635865353354704310040023)
  ·
    refine ⟨5453798030032056465060035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3635865353354704310040023 5453798030032056465060035)
    ·
      refine ⟨8180697045048084697590053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5453798030032056465060035 8180697045048084697590053)
      ·
        refine ⟨1533880695946515880798135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8180697045048084697590053 1533880695946515880798135)
        ·
          refine ⟨2300821043919773821197203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1533880695946515880798135 2300821043919773821197203)
          ·
            refine ⟨3451231565879660731795805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2300821043919773821197203 3451231565879660731795805)
            ·
              refine ⟨1294211837204872774423427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3451231565879660731795805 1294211837204872774423427)
              ·
                refine ⟨1941317755807309161635141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1294211837204872774423427 1941317755807309161635141)
                ·
                  refine ⟨363997079213870467806589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1941317755807309161635141 363997079213870467806589)
                  ·
                    refine ⟨136498904705201425427471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 363997079213870467806589 136498904705201425427471)
                    ·
                      rfl

theorem cell22_398746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 4, 3].length) (baseStart_398746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398746 prefixEnd_398746 := by exact prefixLift 398746
  have htrace : WordTrace (prefixWord ++ tailWord_398746) baseStart_398746 baseEnd_398746 := by
    simpa [prefixWord, tailWord_398746, baseEnd_398746] using wordTrace_append hprefix tailTrace_398746
  have hstable : (prefixWord ++ tailWord_398746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398746).length < 2 ^ (prefixWord ++ tailWord_398746).sum := by decide
  have hdescent : baseEnd_398746 < baseStart_398746 := by decide
  rcases family_descends (prefixWord ++ tailWord_398746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398748 : List Nat := [2, 2, 3, 4, 1, 1, 2, 1, 6]
def baseStart_398748 : Nat := 118140960795 + 398748 * 2 ^ 59
def prefixEnd_398748 : Nat := 4983230072969 + 3 ^ 40 * 398748 * 2
def baseEnd_398748 : Nat := 45499863115358028959155

theorem tailTrace_398748 : CollatzResearch.WordTrace tailWord_398748 prefixEnd_398748 45499863115358028959155 := by
  unfold tailWord_398748
  simp only [CollatzResearch.WordTrace]
  refine ⟨7271767179705785790866449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9695689572941047721155265 7271767179705785790866449)
  ·
    refine ⟨5453825384779339343149837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7271767179705785790866449 5453825384779339343149837)
    ·
      refine ⟨2045184519292252253681189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5453825384779339343149837 2045184519292252253681189)
      ·
        refine ⟨383472097367297297565223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2045184519292252253681189 383472097367297297565223)
        ·
          refine ⟨575208146050945946347835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383472097367297297565223 575208146050945946347835)
          ·
            refine ⟨862812219076418919521753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575208146050945946347835 862812219076418919521753)
            ·
              refine ⟨647109164307314189641315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 862812219076418919521753 647109164307314189641315)
              ·
                refine ⟨970663746460971284461973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 647109164307314189641315 970663746460971284461973)
                ·
                  refine ⟨45499863115358028959155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 970663746460971284461973 45499863115358028959155)
                  ·
                    rfl

theorem cell22_398748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 6].length) (baseStart_398748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398748 prefixEnd_398748 := by exact prefixLift 398748
  have htrace : WordTrace (prefixWord ++ tailWord_398748) baseStart_398748 baseEnd_398748 := by
    simpa [prefixWord, tailWord_398748, baseEnd_398748] using wordTrace_append hprefix tailTrace_398748
  have hstable : (prefixWord ++ tailWord_398748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398748).length < 2 ^ (prefixWord ++ tailWord_398748).sum := by decide
  have hdescent : baseEnd_398748 < baseStart_398748 := by decide
  rcases family_descends (prefixWord ++ tailWord_398748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398759 : List Nat := [1, 1, 6, 1, 1, 1, 2, 9]
def baseStart_398759 : Nat := 118140960795 + 398759 * 2 ^ 59
def prefixEnd_398759 : Nat := 4983230072969 + 3 ^ 40 * 398759 * 2
def baseEnd_398759 : Nat := 15167039430097080539159

theorem tailTrace_398759 : CollatzResearch.WordTrace tailWord_398759 prefixEnd_398759 15167039430097080539159 := by
  unfold tailWord_398759
  simp only [CollatzResearch.WordTrace]
  refine ⟨14543935562371720460383331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9695957041581146973588887 14543935562371720460383331)
  ·
    refine ⟨21815903343557580690574997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14543935562371720460383331 21815903343557580690574997)
    ·
      refine ⟨1022620469229261594870703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21815903343557580690574997 1022620469229261594870703)
      ·
        refine ⟨1533930703843892392306055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1022620469229261594870703 1533930703843892392306055)
        ·
          refine ⟨2300896055765838588459083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1533930703843892392306055 2300896055765838588459083)
          ·
            refine ⟨3451344083648757882688625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2300896055765838588459083 3451344083648757882688625)
            ·
              refine ⟨2588508062736568412016469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3451344083648757882688625 2588508062736568412016469)
              ·
                refine ⟨15167039430097080539159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2588508062736568412016469 15167039430097080539159)
                ·
                  rfl

theorem cell22_398759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 9].length) (baseStart_398759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398759 prefixEnd_398759 := by exact prefixLift 398759
  have htrace : WordTrace (prefixWord ++ tailWord_398759) baseStart_398759 baseEnd_398759 := by
    simpa [prefixWord, tailWord_398759, baseEnd_398759] using wordTrace_append hprefix tailTrace_398759
  have hstable : (prefixWord ++ tailWord_398759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398759).length < 2 ^ (prefixWord ++ tailWord_398759).sum := by decide
  have hdescent : baseEnd_398759 < baseStart_398759 := by decide
  rcases family_descends (prefixWord ++ tailWord_398759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398808 : List Nat := [2, 1, 2, 2, 2, 1, 2, 6, 1, 3]
def baseStart_398808 : Nat := 118140960795 + 398808 * 2 ^ 59
def prefixEnd_398808 : Nat := 4983230072969 + 3 ^ 40 * 398808 * 2
def baseEnd_398808 : Nat := 136520128572253930377281

theorem tailTrace_398808 : CollatzResearch.WordTrace tailWord_398808 prefixEnd_398808 136520128572253930377281 := by
  unfold tailWord_398808
  simp only [CollatzResearch.WordTrace]
  refine ⟨7272861369597100914458539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9697148492796134552611385 7272861369597100914458539)
  ·
    refine ⟨10909292054395651371687809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7272861369597100914458539 10909292054395651371687809)
    ·
      refine ⟨8181969040796738528765857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10909292054395651371687809 8181969040796738528765857)
      ·
        refine ⟨6136476780597553896574393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8181969040796738528765857 6136476780597553896574393)
        ·
          refine ⟨4602357585448165422430795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6136476780597553896574393 4602357585448165422430795)
          ·
            refine ⟨6903536378172248133646193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4602357585448165422430795 6903536378172248133646193)
            ·
              refine ⟨5177652283629186100234645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6903536378172248133646193 5177652283629186100234645)
              ·
                refine ⟨242702450795118098448499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5177652283629186100234645 242702450795118098448499)
                ·
                  refine ⟨364053676192677147672749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 242702450795118098448499 364053676192677147672749)
                  ·
                    refine ⟨136520128572253930377281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 364053676192677147672749 136520128572253930377281)
                    ·
                      rfl

theorem cell22_398808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6, 1, 3].length) (baseStart_398808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398808 prefixEnd_398808 := by exact prefixLift 398808
  have htrace : WordTrace (prefixWord ++ tailWord_398808) baseStart_398808 baseEnd_398808 := by
    simpa [prefixWord, tailWord_398808, baseEnd_398808] using wordTrace_append hprefix tailTrace_398808
  have hstable : (prefixWord ++ tailWord_398808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398808).length < 2 ^ (prefixWord ++ tailWord_398808).sum := by decide
  have hdescent : baseEnd_398808 < baseStart_398808 := by decide
  rcases family_descends (prefixWord ++ tailWord_398808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398859 : List Nat := [1, 1, 1, 1, 9, 1, 2, 2, 1, 3]
def baseStart_398859 : Nat := 118140960795 + 398859 * 2 ^ 59
def prefixEnd_398859 : Nat := 4983230072969 + 3 ^ 40 * 398859 * 2
def baseEnd_398859 : Nat := 136537586914506797352125

theorem tailTrace_398859 : CollatzResearch.WordTrace tailWord_398859 prefixEnd_398859 136537586914506797352125 := by
  unfold tailWord_398859
  simp only [CollatzResearch.WordTrace]
  refine ⟨14547582862009437539023631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9698388574672958359349087 14547582862009437539023631)
  ·
    refine ⟨21821374293014156308535447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14547582862009437539023631 21821374293014156308535447)
    ·
      refine ⟨32732061439521234462803171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21821374293014156308535447 32732061439521234462803171)
      ·
        refine ⟨49098092159281851694204757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32732061439521234462803171 49098092159281851694204757)
        ·
          refine ⟨287684133745792099770731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 49098092159281851694204757 287684133745792099770731)
          ·
            refine ⟨431526200618688149656097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287684133745792099770731 431526200618688149656097)
            ·
              refine ⟨323644650464016112242073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431526200618688149656097 323644650464016112242073)
              ·
                refine ⟨242733487848012084181555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323644650464016112242073 242733487848012084181555)
                ·
                  refine ⟨364100231772018126272333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 242733487848012084181555 364100231772018126272333)
                  ·
                    refine ⟨136537586914506797352125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 364100231772018126272333 136537586914506797352125)
                    ·
                      rfl

theorem cell22_398859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2, 1, 3].length) (baseStart_398859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398859 prefixEnd_398859 := by exact prefixLift 398859
  have htrace : WordTrace (prefixWord ++ tailWord_398859) baseStart_398859 baseEnd_398859 := by
    simpa [prefixWord, tailWord_398859, baseEnd_398859] using wordTrace_append hprefix tailTrace_398859
  have hstable : (prefixWord ++ tailWord_398859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398859).length < 2 ^ (prefixWord ++ tailWord_398859).sum := by decide
  have hdescent : baseEnd_398859 < baseStart_398859 := by decide
  rcases family_descends (prefixWord ++ tailWord_398859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398881 : List Nat := [1, 2, 3, 2, 2, 2, 1, 3, 1, 5]
def baseStart_398881 : Nat := 118140960795 + 398881 * 2 ^ 59
def prefixEnd_398881 : Nat := 4983230072969 + 3 ^ 40 * 398881 * 2
def baseEnd_398881 : Nat := 136545117964106073302057

theorem tailTrace_398881 : CollatzResearch.WordTrace tailWord_398881 prefixEnd_398881 136545117964106073302057 := by
  unfold tailWord_398881
  simp only [CollatzResearch.WordTrace]
  refine ⟨14548385267929735296324497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9698923511953156864216331 14548385267929735296324497)
  ·
    refine ⟨10911288950947301472243373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14548385267929735296324497 10911288950947301472243373)
    ·
      refine ⟨4091733356605238052091265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10911288950947301472243373 4091733356605238052091265)
      ·
        refine ⟨3068800017453928539068449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4091733356605238052091265 3068800017453928539068449)
        ·
          refine ⟨2301600013090446404301337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3068800017453928539068449 2301600013090446404301337)
          ·
            refine ⟨1726200009817834803226003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2301600013090446404301337 1726200009817834803226003)
            ·
              refine ⟨2589300014726752204839005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1726200009817834803226003 2589300014726752204839005)
              ·
                refine ⟨970987505522532076814627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2589300014726752204839005 970987505522532076814627)
                ·
                  refine ⟨1456481258283798115221941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 970987505522532076814627 1456481258283798115221941)
                  ·
                    refine ⟨136545117964106073302057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1456481258283798115221941 136545117964106073302057)
                    ·
                      rfl

theorem cell22_398881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_398881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398881 prefixEnd_398881 := by exact prefixLift 398881
  have htrace : WordTrace (prefixWord ++ tailWord_398881) baseStart_398881 baseEnd_398881 := by
    simpa [prefixWord, tailWord_398881, baseEnd_398881] using wordTrace_append hprefix tailTrace_398881
  have hstable : (prefixWord ++ tailWord_398881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398881).length < 2 ^ (prefixWord ++ tailWord_398881).sum := by decide
  have hdescent : baseEnd_398881 < baseStart_398881 := by decide
  rcases family_descends (prefixWord ++ tailWord_398881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398990 : List Nat := [4, 1, 1, 3, 1, 2, 4, 1, 5]
def baseStart_398990 : Nat := 118140960795 + 398990 * 2 ^ 59
def prefixEnd_398990 : Nat := 4983230072969 + 3 ^ 40 * 398990 * 2
def baseEnd_398990 : Nat := 45527476963888707442241

theorem tailTrace_398990 : CollatzResearch.WordTrace tailWord_398990 prefixEnd_398990 45527476963888707442241 := by
  unfold tailWord_398990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1819045103066855864005303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9701573883023231274694949 1819045103066855864005303)
  ·
    refine ⟨2728567654600283796007955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1819045103066855864005303 2728567654600283796007955)
    ·
      refine ⟨4092851481900425694011933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2728567654600283796007955 4092851481900425694011933)
      ·
        refine ⟨1534819305712659635254475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4092851481900425694011933 1534819305712659635254475)
        ·
          refine ⟨2302228958568989452881713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1534819305712659635254475 2302228958568989452881713)
          ·
            refine ⟨1726671718926742089661285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2302228958568989452881713 1726671718926742089661285)
            ·
              refine ⟨323750947298764141811491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1726671718926742089661285 323750947298764141811491)
              ·
                refine ⟨485626420948146212717237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323750947298764141811491 485626420948146212717237)
                ·
                  refine ⟨45527476963888707442241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 485626420948146212717237 45527476963888707442241)
                  ·
                    rfl

theorem cell22_398990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_398990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_398990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_398990 prefixEnd_398990 := by exact prefixLift 398990
  have htrace : WordTrace (prefixWord ++ tailWord_398990) baseStart_398990 baseEnd_398990 := by
    simpa [prefixWord, tailWord_398990, baseEnd_398990] using wordTrace_append hprefix tailTrace_398990
  have hstable : (prefixWord ++ tailWord_398990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398990).length < 2 ^ (prefixWord ++ tailWord_398990).sum := by decide
  have hdescent : baseEnd_398990 < baseStart_398990 := by decide
  rcases family_descends (prefixWord ++ tailWord_398990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399033 : List Nat := [1, 2, 1, 4, 1, 1, 2, 3, 4, 3]
def baseStart_399033 : Nat := 118140960795 + 399033 * 2 ^ 59
def prefixEnd_399033 : Nat := 4983230072969 + 3 ^ 40 * 399033 * 2
def baseEnd_399033 : Nat := 136597150670428343501591

theorem tailTrace_399033 : CollatzResearch.WordTrace tailWord_399033 prefixEnd_399033 136597150670428343501591 := by
  unfold tailWord_399033
  simp only [CollatzResearch.WordTrace]
  refine ⟨14553929163379065255857753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9702619442252710170571835 14553929163379065255857753)
  ·
    refine ⟨10915446872534298941893315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14553929163379065255857753 10915446872534298941893315)
    ·
      refine ⟨16373170308801448412839973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10915446872534298941893315 16373170308801448412839973)
      ·
        refine ⟨3069969432900271577407495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16373170308801448412839973 3069969432900271577407495)
        ·
          refine ⟨4604954149350407366111243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3069969432900271577407495 4604954149350407366111243)
          ·
            refine ⟨6907431224025611049166865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4604954149350407366111243 6907431224025611049166865)
            ·
              refine ⟨5180573418019208286875149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6907431224025611049166865 5180573418019208286875149)
              ·
                refine ⟨1942715031757203107578181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5180573418019208286875149 1942715031757203107578181)
                ·
                  refine ⟨364259068454475582670909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1942715031757203107578181 364259068454475582670909)
                  ·
                    refine ⟨136597150670428343501591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 364259068454475582670909 136597150670428343501591)
                    ·
                      rfl

theorem cell22_399033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4, 3].length) (baseStart_399033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_399033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_399033 prefixEnd_399033 := by exact prefixLift 399033
  have htrace : WordTrace (prefixWord ++ tailWord_399033) baseStart_399033 baseEnd_399033 := by
    simpa [prefixWord, tailWord_399033, baseEnd_399033] using wordTrace_append hprefix tailTrace_399033
  have hstable : (prefixWord ++ tailWord_399033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399033).length < 2 ^ (prefixWord ++ tailWord_399033).sum := by decide
  have hdescent : baseEnd_399033 < baseStart_399033 := by decide
  rcases family_descends (prefixWord ++ tailWord_399033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399050 : List Nat := [3, 1, 2, 1, 5, 1, 2, 1, 1, 5]
def baseStart_399050 : Nat := 118140960795 + 399050 * 2 ^ 59
def prefixEnd_399050 : Nat := 4983230072969 + 3 ^ 40 * 399050 * 2
def baseEnd_399050 : Nat := 136602970117845965826539

theorem tailTrace_399050 : CollatzResearch.WordTrace tailWord_399050 prefixEnd_399050 136602970117845965826539 := by
  unfold tailWord_399050
  simp only [CollatzResearch.WordTrace]
  refine ⟨3638637301079369289806651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9703032802878318106151069 3638637301079369289806651)
  ·
    refine ⟨5457955951619053934709977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3638637301079369289806651 5457955951619053934709977)
    ·
      refine ⟨4093466963714290451032483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5457955951619053934709977 4093466963714290451032483)
      ·
        refine ⟨6140200445571435676548725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4093466963714290451032483 6140200445571435676548725)
        ·
          refine ⟨575643791772322094676443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6140200445571435676548725 575643791772322094676443)
          ·
            refine ⟨863465687658483142014665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575643791772322094676443 863465687658483142014665)
            ·
              refine ⟨647599265743862356510999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 863465687658483142014665 647599265743862356510999)
              ·
                refine ⟨971398898615793534766499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 647599265743862356510999 971398898615793534766499)
                ·
                  refine ⟨1457098347923690302149749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 971398898615793534766499 1457098347923690302149749)
                  ·
                    refine ⟨136602970117845965826539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1457098347923690302149749 136602970117845965826539)
                    ·
                      rfl

theorem cell22_399050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_399050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_399050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_399050 prefixEnd_399050 := by exact prefixLift 399050
  have htrace : WordTrace (prefixWord ++ tailWord_399050) baseStart_399050 baseEnd_399050 := by
    simpa [prefixWord, tailWord_399050, baseEnd_399050] using wordTrace_append hprefix tailTrace_399050
  have hstable : (prefixWord ++ tailWord_399050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399050).length < 2 ^ (prefixWord ++ tailWord_399050).sum := by decide
  have hdescent : baseEnd_399050 < baseStart_399050 := by decide
  rcases family_descends (prefixWord ++ tailWord_399050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399063 : List Nat := [1, 1, 3, 2, 1, 3, 5, 6]
def baseStart_399063 : Nat := 118140960795 + 399063 * 2 ^ 59
def prefixEnd_399063 : Nat := 4983230072969 + 3 ^ 40 * 399063 * 2
def baseEnd_399063 : Nat := 15178602253724251694611

theorem tailTrace_399063 : CollatzResearch.WordTrace tailWord_399063 prefixEnd_399063 15178602253724251694611 := by
  unfold tailWord_399063
  simp only [CollatzResearch.WordTrace]
  refine ⟨14555023353270380379449843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9703348902180253586299895 14555023353270380379449843)
  ·
    refine ⟨21832535029905570569174765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14555023353270380379449843 21832535029905570569174765)
    ·
      refine ⟨8187200636214588963440537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21832535029905570569174765 8187200636214588963440537)
      ·
        refine ⟨6140400477160941722580403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8187200636214588963440537 6140400477160941722580403)
        ·
          refine ⟨9210600715741412583870605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6140400477160941722580403 9210600715741412583870605)
          ·
            refine ⟨3453975268403029718951477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9210600715741412583870605 3453975268403029718951477)
            ·
              refine ⟨323810181412784036151701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3453975268403029718951477 323810181412784036151701)
              ·
                refine ⟨15178602253724251694611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 323810181412784036151701 15178602253724251694611)
                ·
                  rfl

theorem cell22_399063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 6].length) (baseStart_399063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_399063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_399063 prefixEnd_399063 := by exact prefixLift 399063
  have htrace : WordTrace (prefixWord ++ tailWord_399063) baseStart_399063 baseEnd_399063 := by
    simpa [prefixWord, tailWord_399063, baseEnd_399063] using wordTrace_append hprefix tailTrace_399063
  have hstable : (prefixWord ++ tailWord_399063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399063).length < 2 ^ (prefixWord ++ tailWord_399063).sum := by decide
  have hdescent : baseEnd_399063 < baseStart_399063 := by decide
  rcases family_descends (prefixWord ++ tailWord_399063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399065 : List Nat := [1, 2, 1, 2, 3, 5, 1, 1, 2, 4]
def baseStart_399065 : Nat := 118140960795 + 399065 * 2 ^ 59
def prefixEnd_399065 : Nat := 4983230072969 + 3 ^ 40 * 399065 * 2
def baseEnd_399065 : Nat := 136608104924390926701493

theorem tailTrace_399065 : CollatzResearch.WordTrace tailWord_399065 prefixEnd_399065 136608104924390926701493 := by
  unfold tailWord_399065
  simp only [CollatzResearch.WordTrace]
  refine ⟨14555096299263134721022649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9703397532842089814015099 14555096299263134721022649)
  ·
    refine ⟨10916322224447351040766987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14555096299263134721022649 10916322224447351040766987)
    ·
      refine ⟨16374483336671026561150481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10916322224447351040766987 16374483336671026561150481)
      ·
        refine ⟨12280862502503269920862861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16374483336671026561150481 12280862502503269920862861)
        ·
          refine ⟨4605323438438726220323573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12280862502503269920862861 4605323438438726220323573)
          ·
            refine ⟨431749072353630583155335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4605323438438726220323573 431749072353630583155335)
            ·
              refine ⟨647623608530445874733003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431749072353630583155335 647623608530445874733003)
              ·
                refine ⟨971435412795668812099505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 647623608530445874733003 971435412795668812099505)
                ·
                  refine ⟨728576559596751609074629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 971435412795668812099505 728576559596751609074629)
                  ·
                    refine ⟨136608104924390926701493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 728576559596751609074629 136608104924390926701493)
                    ·
                      rfl

theorem cell22_399065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 4].length) (baseStart_399065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_399065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_399065 prefixEnd_399065 := by exact prefixLift 399065
  have htrace : WordTrace (prefixWord ++ tailWord_399065) baseStart_399065 baseEnd_399065 := by
    simpa [prefixWord, tailWord_399065, baseEnd_399065] using wordTrace_append hprefix tailTrace_399065
  have hstable : (prefixWord ++ tailWord_399065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399065).length < 2 ^ (prefixWord ++ tailWord_399065).sum := by decide
  have hdescent : baseEnd_399065 < baseStart_399065 := by decide
  rcases family_descends (prefixWord ++ tailWord_399065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399069 : List Nat := [1, 4, 3, 3, 1, 1, 2, 3, 4]
def baseStart_399069 : Nat := 118140960795 + 399069 * 2 ^ 59
def prefixEnd_399069 : Nat := 4983230072969 + 3 ^ 40 * 399069 * 2
def baseEnd_399069 : Nat := 45536491402045416533827

theorem tailTrace_399069 : CollatzResearch.WordTrace tailWord_399069 prefixEnd_399069 45536491402045416533827 := by
  unfold tailWord_399069
  simp only [CollatzResearch.WordTrace]
  refine ⟨14555242191248643404168261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9703494794165762269445507 14555242191248643404168261)
  ·
    refine ⟨2729107910859120638281549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14555242191248643404168261 2729107910859120638281549)
    ·
      refine ⟨1023415466572170239355581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2729107910859120638281549 1023415466572170239355581)
      ·
        refine ⟨383780799964563839758343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1023415466572170239355581 383780799964563839758343)
        ·
          refine ⟨575671199946845759637515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383780799964563839758343 575671199946845759637515)
          ·
            refine ⟨863506799920268639456273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575671199946845759637515 863506799920268639456273)
            ·
              refine ⟨647630099940201479592205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 863506799920268639456273 647630099940201479592205)
              ·
                refine ⟨242861287477575554847077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 647630099940201479592205 242861287477575554847077)
                ·
                  refine ⟨45536491402045416533827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 242861287477575554847077 45536491402045416533827)
                  ·
                    rfl

theorem cell22_399069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_399069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_399069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_399069 prefixEnd_399069 := by exact prefixLift 399069
  have htrace : WordTrace (prefixWord ++ tailWord_399069) baseStart_399069 baseEnd_399069 := by
    simpa [prefixWord, tailWord_399069, baseEnd_399069] using wordTrace_append hprefix tailTrace_399069
  have hstable : (prefixWord ++ tailWord_399069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399069).length < 2 ^ (prefixWord ++ tailWord_399069).sum := by decide
  have hdescent : baseEnd_399069 < baseStart_399069 := by decide
  rcases family_descends (prefixWord ++ tailWord_399069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399185 : List Nat := [1, 2, 2, 1, 5, 2, 1, 2, 1, 5]
def baseStart_399185 : Nat := 118140960795 + 399185 * 2 ^ 59
def prefixEnd_399185 : Nat := 4983230072969 + 3 ^ 40 * 399185 * 2
def baseEnd_399185 : Nat := 136649183376750613701125

theorem tailTrace_399185 : CollatzResearch.WordTrace tailWord_399185 prefixEnd_399185 136649183376750613701125 := by
  unfold tailWord_399185
  simp only [CollatzResearch.WordTrace]
  refine ⟨14559473058828395215391009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9706315372552263476927339 14559473058828395215391009)
  ·
    refine ⟨10919604794121296411543257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14559473058828395215391009 10919604794121296411543257)
    ·
      refine ⟨8189703595590972308657443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10919604794121296411543257 8189703595590972308657443)
      ·
        refine ⟨12284555393386458462986165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8189703595590972308657443 12284555393386458462986165)
        ·
          refine ⟨1151677068129980480904953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12284555393386458462986165 1151677068129980480904953)
          ·
            refine ⟨863757801097485360678715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1151677068129980480904953 863757801097485360678715)
            ·
              refine ⟨1295636701646228041018073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 863757801097485360678715 1295636701646228041018073)
              ·
                refine ⟨971727526234671030763555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1295636701646228041018073 971727526234671030763555)
                ·
                  refine ⟨1457591289352006546145333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 971727526234671030763555 1457591289352006546145333)
                  ·
                    refine ⟨136649183376750613701125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1457591289352006546145333 136649183376750613701125)
                    ·
                      rfl

theorem cell22_399185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_399185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_399185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_399185 prefixEnd_399185 := by exact prefixLift 399185
  have htrace : WordTrace (prefixWord ++ tailWord_399185) baseStart_399185 baseEnd_399185 := by
    simpa [prefixWord, tailWord_399185, baseEnd_399185] using wordTrace_append hprefix tailTrace_399185
  have hstable : (prefixWord ++ tailWord_399185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399185).length < 2 ^ (prefixWord ++ tailWord_399185).sum := by decide
  have hdescent : baseEnd_399185 < baseStart_399185 := by decide
  rcases family_descends (prefixWord ++ tailWord_399185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399200 : List Nat := [2, 1, 1, 3, 3, 2, 2, 2, 2, 4]
def baseStart_399200 : Nat := 118140960795 + 399200 * 2 ^ 59
def prefixEnd_399200 : Nat := 4983230072969 + 3 ^ 40 * 399200 * 2
def baseEnd_399200 : Nat := 136654318183295574576079

theorem tailTrace_399200 : CollatzResearch.WordTrace tailWord_399200 prefixEnd_399200 136654318183295574576079 := by
  unfold tailWord_399200
  simp only [CollatzResearch.WordTrace]
  refine ⟨7280010076887026388593527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9706680102516035184791369 7280010076887026388593527)
  ·
    refine ⟨10920015115330539582890291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7280010076887026388593527 10920015115330539582890291)
    ·
      refine ⟨16380022672995809374335437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10920015115330539582890291 16380022672995809374335437)
      ·
        refine ⟨6142508502373428515375789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16380022672995809374335437 6142508502373428515375789)
        ·
          refine ⟨2303440688390035693265921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6142508502373428515375789 2303440688390035693265921)
          ·
            refine ⟨1727580516292526769949441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2303440688390035693265921 1727580516292526769949441)
            ·
              refine ⟨1295685387219395077462081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1727580516292526769949441 1295685387219395077462081)
              ·
                refine ⟨971764040414546308096561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1295685387219395077462081 971764040414546308096561)
                ·
                  refine ⟨728823030310909731072421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 971764040414546308096561 728823030310909731072421)
                  ·
                    refine ⟨136654318183295574576079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 728823030310909731072421 136654318183295574576079)
                    ·
                      rfl

theorem cell22_399200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 2, 4].length) (baseStart_399200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_399200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_399200 prefixEnd_399200 := by exact prefixLift 399200
  have htrace : WordTrace (prefixWord ++ tailWord_399200) baseStart_399200 baseEnd_399200 := by
    simpa [prefixWord, tailWord_399200, baseEnd_399200] using wordTrace_append hprefix tailTrace_399200
  have hstable : (prefixWord ++ tailWord_399200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399200).length < 2 ^ (prefixWord ++ tailWord_399200).sum := by decide
  have hdescent : baseEnd_399200 < baseStart_399200 := by decide
  rcases family_descends (prefixWord ++ tailWord_399200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399243 : List Nat := [1, 1, 1, 1, 4, 2, 1, 4, 7]
def baseStart_399243 : Nat := 118140960795 + 399243 * 2 ^ 59
def prefixEnd_399243 : Nat := 4983230072969 + 3 ^ 40 * 399243 * 2
def baseEnd_399243 : Nat := 45556345987352598583649

theorem tailTrace_399243 : CollatzResearch.WordTrace tailWord_399243 prefixEnd_399243 45556345987352598583649 := by
  unfold tailWord_399243
  simp only [CollatzResearch.WordTrace]
  refine ⟨14561588492618271121002383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9707725661745514080668255 14561588492618271121002383)
  ·
    refine ⟨21842382738927406681503575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14561588492618271121002383 21842382738927406681503575)
    ·
      refine ⟨32763574108391110022255363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21842382738927406681503575 32763574108391110022255363)
      ·
        refine ⟨49145361162586665033383045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32763574108391110022255363 49145361162586665033383045)
        ·
          refine ⟨9214755217984999693759321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49145361162586665033383045 9214755217984999693759321)
          ·
            refine ⟨6911066413488749770319491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9214755217984999693759321 6911066413488749770319491)
            ·
              refine ⟨10366599620233124655479237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6911066413488749770319491 10366599620233124655479237)
              ·
                refine ⟨1943737428793710872902357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10366599620233124655479237 1943737428793710872902357)
                ·
                  refine ⟨45556345987352598583649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1943737428793710872902357 45556345987352598583649)
                  ·
                    rfl

theorem cell22_399243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 7].length) (baseStart_399243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_399243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_399243 prefixEnd_399243 := by exact prefixLift 399243
  have htrace : WordTrace (prefixWord ++ tailWord_399243) baseStart_399243 baseEnd_399243 := by
    simpa [prefixWord, tailWord_399243, baseEnd_399243] using wordTrace_append hprefix tailTrace_399243
  have hstable : (prefixWord ++ tailWord_399243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399243).length < 2 ^ (prefixWord ++ tailWord_399243).sum := by decide
  have hdescent : baseEnd_399243 < baseStart_399243 := by decide
  rcases family_descends (prefixWord ++ tailWord_399243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399273 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 2, 8]
def baseStart_399273 : Nat := 118140960795 + 399273 * 2 ^ 59
def prefixEnd_399273 : Nat := 4983230072969 + 3 ^ 40 * 399273 * 2
def baseEnd_399273 : Nat := 136679307575147717500855

theorem tailTrace_399273 : CollatzResearch.WordTrace tailWord_399273 prefixEnd_399273 136679307575147717500855 := by
  unfold tailWord_399273
  simp only [CollatzResearch.WordTrace]
  refine ⟨14562682682509586244594473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9708455121673057496396315 14562682682509586244594473)
  ·
    refine ⟨10922012011882189683445855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14562682682509586244594473 10922012011882189683445855)
    ·
      refine ⟨16383018017823284525168783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10922012011882189683445855 16383018017823284525168783)
      ·
        refine ⟨24574527026734926787753175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16383018017823284525168783 24574527026734926787753175)
        ·
          refine ⟨36861790540102390181629763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24574527026734926787753175 36861790540102390181629763)
          ·
            refine ⟨55292685810153585272444645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36861790540102390181629763 55292685810153585272444645)
            ·
              refine ⟨10367378589403797238583371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55292685810153585272444645 10367378589403797238583371)
              ·
                refine ⟨15551067884105695857875057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10367378589403797238583371 15551067884105695857875057)
                ·
                  refine ⟨11663300913079271893406293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15551067884105695857875057 11663300913079271893406293)
                  ·
                    refine ⟨136679307575147717500855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11663300913079271893406293 136679307575147717500855)
                    ·
                      rfl

theorem cell22_399273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 8].length) (baseStart_399273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_399273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_399273 prefixEnd_399273 := by exact prefixLift 399273
  have htrace : WordTrace (prefixWord ++ tailWord_399273) baseStart_399273 baseEnd_399273 := by
    simpa [prefixWord, tailWord_399273, baseEnd_399273] using wordTrace_append hprefix tailTrace_399273
  have hstable : (prefixWord ++ tailWord_399273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399273).length < 2 ^ (prefixWord ++ tailWord_399273).sum := by decide
  have hdescent : baseEnd_399273 < baseStart_399273 := by decide
  rcases family_descends (prefixWord ++ tailWord_399273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399366 : List Nat := [6, 2, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_399366 : Nat := 118140960795 + 399366 * 2 ^ 59
def prefixEnd_399366 : Nat := 4983230072969 + 3 ^ 40 * 399366 * 2
def baseEnd_399366 : Nat := 136711143375726474925571

theorem tailTrace_399366 : CollatzResearch.WordTrace tailWord_399366 prefixEnd_399366 136711143375726474925571 := by
  unfold tailWord_399366
  simp only [CollatzResearch.WordTrace]
  refine ⟨455189833474145722741561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9710716447448442085153301 455189833474145722741561)
  ·
    refine ⟨341392375105609292056171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 455189833474145722741561 341392375105609292056171)
    ·
      refine ⟨512088562658413938084257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341392375105609292056171 512088562658413938084257)
      ·
        refine ⟨384066421993810453563193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 512088562658413938084257 384066421993810453563193)
        ·
          refine ⟨288049816495357840172395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384066421993810453563193 288049816495357840172395)
          ·
            refine ⟨432074724743036760258593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288049816495357840172395 432074724743036760258593)
            ·
              refine ⟨324056043557277570193945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432074724743036760258593 324056043557277570193945)
              ·
                refine ⟨243042032667958177645459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 324056043557277570193945 243042032667958177645459)
                ·
                  refine ⟨364563049001937266468189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243042032667958177645459 364563049001937266468189)
                  ·
                    refine ⟨136711143375726474925571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 364563049001937266468189 136711143375726474925571)
                    ·
                      rfl

theorem cell22_399366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_399366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_399366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_399366 prefixEnd_399366 := by exact prefixLift 399366
  have htrace : WordTrace (prefixWord ++ tailWord_399366) baseStart_399366 baseEnd_399366 := by
    simpa [prefixWord, tailWord_399366, baseEnd_399366] using wordTrace_append hprefix tailTrace_399366
  have hstable : (prefixWord ++ tailWord_399366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399366).length < 2 ^ (prefixWord ++ tailWord_399366).sum := by decide
  have hdescent : baseEnd_399366 < baseStart_399366 := by decide
  rcases family_descends (prefixWord ++ tailWord_399366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399491 : List Nat := [1, 1, 1, 3, 3, 4, 3, 2, 4]
def baseStart_399491 : Nat := 118140960795 + 399491 * 2 ^ 59
def prefixEnd_399491 : Nat := 4983230072969 + 3 ^ 40 * 399491 * 2
def baseEnd_399491 : Nat := 45584644476755938516729

theorem tailTrace_399491 : CollatzResearch.WordTrace tailWord_399491 prefixEnd_399491 45584644476755938516729 := by
  unfold tailWord_399491
  simp only [CollatzResearch.WordTrace]
  refine ⟨14570633795719809476030327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9713755863813206317353551 14570633795719809476030327)
  ·
    refine ⟨21855950693579714214045491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14570633795719809476030327 21855950693579714214045491)
    ·
      refine ⟨32783926040369571321068237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21855950693579714214045491 32783926040369571321068237)
      ·
        refine ⟨12293972265138589245400589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32783926040369571321068237 12293972265138589245400589)
        ·
          refine ⟨4610239599426970967025221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12293972265138589245400589 4610239599426970967025221)
          ·
            refine ⟨864419924892557056317229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4610239599426970967025221 864419924892557056317229)
            ·
              refine ⟨324157471834708896118961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 864419924892557056317229 324157471834708896118961)
              ·
                refine ⟨243118103876031672089221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 324157471834708896118961 243118103876031672089221)
                ·
                  refine ⟨45584644476755938516729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 243118103876031672089221 45584644476755938516729)
                  ·
                    rfl

theorem cell22_399491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2, 4].length) (baseStart_399491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_399491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_399491 prefixEnd_399491 := by exact prefixLift 399491
  have htrace : WordTrace (prefixWord ++ tailWord_399491) baseStart_399491 baseEnd_399491 := by
    simpa [prefixWord, tailWord_399491, baseEnd_399491] using wordTrace_append hprefix tailTrace_399491
  have hstable : (prefixWord ++ tailWord_399491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399491).length < 2 ^ (prefixWord ++ tailWord_399491).sum := by decide
  have hdescent : baseEnd_399491 < baseStart_399491 := by decide
  rcases family_descends (prefixWord ++ tailWord_399491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399506 : List Nat := [3, 2, 3, 1, 1, 1, 3, 3, 2, 3]
def baseStart_399506 : Nat := 118140960795 + 399506 * 2 ^ 59
def prefixEnd_399506 : Nat := 4983230072969 + 3 ^ 40 * 399506 * 2
def baseEnd_399506 : Nat := 136759068236812776425141

theorem tailTrace_399506 : CollatzResearch.WordTrace tailWord_399506 prefixEnd_399506 136759068236812776425141 := by
  unfold tailWord_399506
  simp only [CollatzResearch.WordTrace]
  refine ⟨3642795222666366759456593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9714120593776978025217581 3642795222666366759456593)
  ·
    refine ⟨2732096416999775069592445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3642795222666366759456593 2732096416999775069592445)
    ·
      refine ⟨1024536156374915651097167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2732096416999775069592445 1024536156374915651097167)
      ·
        refine ⟨1536804234562373476645751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1024536156374915651097167 1536804234562373476645751)
        ·
          refine ⟨2305206351843560214968627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1536804234562373476645751 2305206351843560214968627)
          ·
            refine ⟨3457809527765340322452941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2305206351843560214968627 3457809527765340322452941)
            ·
              refine ⟨1296678572912002620919853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3457809527765340322452941 1296678572912002620919853)
              ·
                refine ⟨486254464842000982844945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1296678572912002620919853 486254464842000982844945)
                ·
                  refine ⟨364690848631500737133709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486254464842000982844945 364690848631500737133709)
                  ·
                    refine ⟨136759068236812776425141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 364690848631500737133709 136759068236812776425141)
                    ·
                      rfl

theorem cell22_399506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_399506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_399506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_399506 prefixEnd_399506 := by exact prefixLift 399506
  have htrace : WordTrace (prefixWord ++ tailWord_399506) baseStart_399506 baseEnd_399506 := by
    simpa [prefixWord, tailWord_399506, baseEnd_399506] using wordTrace_append hprefix tailTrace_399506
  have hstable : (prefixWord ++ tailWord_399506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399506).length < 2 ^ (prefixWord ++ tailWord_399506).sum := by decide
  have hdescent : baseEnd_399506 < baseStart_399506 := by decide
  rcases family_descends (prefixWord ++ tailWord_399506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399553 : List Nat := [1, 2, 6, 1, 3, 1, 1, 7]
def baseStart_399553 : Nat := 118140960795 + 399553 * 2 ^ 59
def prefixEnd_399553 : Nat := 4983230072969 + 3 ^ 40 * 399553 * 2
def baseEnd_399553 : Nat := 15197239699702257833333

theorem tailTrace_399553 : CollatzResearch.WordTrace tailWord_399553 prefixEnd_399553 15197239699702257833333 := by
  unfold tailWord_399553
  simp only [CollatzResearch.WordTrace]
  refine ⟨14572895121495194064787313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9715263414330129376524875 14572895121495194064787313)
  ·
    refine ⟨10929671341121395548590485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14572895121495194064787313 10929671341121395548590485)
    ·
      refine ⟨512328344115065416340179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10929671341121395548590485 512328344115065416340179)
      ·
        refine ⟨768492516172598124510269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512328344115065416340179 768492516172598124510269)
        ·
          refine ⟨288184693564724296691351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 768492516172598124510269 288184693564724296691351)
          ·
            refine ⟨432277040347086445037027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288184693564724296691351 432277040347086445037027)
            ·
              refine ⟨648415560520629667555541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432277040347086445037027 648415560520629667555541)
              ·
                refine ⟨15197239699702257833333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 648415560520629667555541 15197239699702257833333)
                ·
                  rfl

theorem cell22_399553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 7].length) (baseStart_399553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_399553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_399553 prefixEnd_399553 := by exact prefixLift 399553
  have htrace : WordTrace (prefixWord ++ tailWord_399553) baseStart_399553 baseEnd_399553 := by
    simpa [prefixWord, tailWord_399553, baseEnd_399553] using wordTrace_append hprefix tailTrace_399553
  have hstable : (prefixWord ++ tailWord_399553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399553).length < 2 ^ (prefixWord ++ tailWord_399553).sum := by decide
  have hdescent : baseEnd_399553 < baseStart_399553 := by decide
  rcases family_descends (prefixWord ++ tailWord_399553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399639 : List Nat := [1, 1, 3, 4, 1, 2, 2, 1, 1, 6]
def baseStart_399639 : Nat := 118140960795 + 399639 * 2 ^ 59
def prefixEnd_399639 : Nat := 4983230072969 + 3 ^ 40 * 399639 * 2
def baseEnd_399639 : Nat := 136804596854844762849733

theorem tailTrace_399639 : CollatzResearch.WordTrace tailWord_399639 prefixEnd_399639 136804596854844762849733 := by
  unfold tailWord_399639
  simp only [CollatzResearch.WordTrace]
  refine ⟨14576031799183630752417971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9717354532789087168278647 14576031799183630752417971)
  ·
    refine ⟨21864047698775446128626957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14576031799183630752417971 21864047698775446128626957)
    ·
      refine ⟨8199017887040792298235109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21864047698775446128626957 8199017887040792298235109)
      ·
        refine ⟨1537315853820148555919083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8199017887040792298235109 1537315853820148555919083)
        ·
          refine ⟨2305973780730222833878625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1537315853820148555919083 2305973780730222833878625)
          ·
            refine ⟨1729480335547667125408969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2305973780730222833878625 1729480335547667125408969)
            ·
              refine ⟨1297110251660750344056727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1729480335547667125408969 1297110251660750344056727)
              ·
                refine ⟨1945665377491125516085091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1297110251660750344056727 1945665377491125516085091)
                ·
                  refine ⟨2918498066236688274127637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1945665377491125516085091 2918498066236688274127637)
                  ·
                    refine ⟨136804596854844762849733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2918498066236688274127637 136804596854844762849733)
                    ·
                      rfl

theorem cell22_399639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_399639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_399639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_399639 prefixEnd_399639 := by exact prefixLift 399639
  have htrace : WordTrace (prefixWord ++ tailWord_399639) baseStart_399639 baseEnd_399639 := by
    simpa [prefixWord, tailWord_399639, baseEnd_399639] using wordTrace_append hprefix tailTrace_399639
  have hstable : (prefixWord ++ tailWord_399639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399639).length < 2 ^ (prefixWord ++ tailWord_399639).sum := by decide
  have hdescent : baseEnd_399639 < baseStart_399639 := by decide
  rcases family_descends (prefixWord ++ tailWord_399639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399703 : List Nat := [1, 1, 3, 2, 3, 1, 2, 5, 1, 3]
def baseStart_399703 : Nat := 118140960795 + 399703 * 2 ^ 59
def prefixEnd_399703 : Nat := 4983230072969 + 3 ^ 40 * 399703 * 2
def baseEnd_399703 : Nat := 136826505362769929249537

theorem tailTrace_399703 : CollatzResearch.WordTrace tailWord_399703 prefixEnd_399703 136826505362769929249537 := by
  unfold tailWord_399703
  simp only [CollatzResearch.WordTrace]
  refine ⟨14578366070951769682747763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9718910713967846455165175 14578366070951769682747763)
  ·
    refine ⟨21867549106427654524121645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14578366070951769682747763 21867549106427654524121645)
    ·
      refine ⟨8200330914910370446545617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21867549106427654524121645 8200330914910370446545617)
      ·
        refine ⟨6150248186182777834909213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8200330914910370446545617 6150248186182777834909213)
        ·
          refine ⟨2306343069818541688090955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6150248186182777834909213 2306343069818541688090955)
          ·
            refine ⟨3459514604727812532136433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2306343069818541688090955 3459514604727812532136433)
            ·
              refine ⟨2594635953545859399102325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3459514604727812532136433 2594635953545859399102325)
              ·
                refine ⟨243247120644924318665843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2594635953545859399102325 243247120644924318665843)
                ·
                  refine ⟨364870680967386477998765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243247120644924318665843 364870680967386477998765)
                  ·
                    refine ⟨136826505362769929249537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 364870680967386477998765 136826505362769929249537)
                    ·
                      rfl

theorem cell22_399703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5, 1, 3].length) (baseStart_399703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_399703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_399703 prefixEnd_399703 := by exact prefixLift 399703
  have htrace : WordTrace (prefixWord ++ tailWord_399703) baseStart_399703 baseEnd_399703 := by
    simpa [prefixWord, tailWord_399703, baseEnd_399703] using wordTrace_append hprefix tailTrace_399703
  have hstable : (prefixWord ++ tailWord_399703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399703).length < 2 ^ (prefixWord ++ tailWord_399703).sum := by decide
  have hdescent : baseEnd_399703 < baseStart_399703 := by decide
  rcases family_descends (prefixWord ++ tailWord_399703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399716 : List Nat := [2, 3, 1, 1, 3, 1, 4, 2, 5]
def baseStart_399716 : Nat := 118140960795 + 399716 * 2 ^ 59
def prefixEnd_399716 : Nat := 4983230072969 + 3 ^ 40 * 399716 * 2
def baseEnd_399716 : Nat := 45610318509480742891499

theorem tailTrace_399716 : CollatzResearch.WordTrace tailWord_399716 prefixEnd_399716 45610318509480742891499 := by
  unfold tailWord_399716
  simp only [CollatzResearch.WordTrace]
  refine ⟨7289420109952336451485501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9719226813269781935314001 7289420109952336451485501)
  ·
    refine ⟨2733532541232126169307063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7289420109952336451485501 2733532541232126169307063)
    ·
      refine ⟨4100298811848189253960595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2733532541232126169307063 4100298811848189253960595)
      ·
        refine ⟨6150448217772283880940893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4100298811848189253960595 6150448217772283880940893)
        ·
          refine ⟨2306418081664606455352835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6150448217772283880940893 2306418081664606455352835)
          ·
            refine ⟨3459627122496909683029253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2306418081664606455352835 3459627122496909683029253)
            ·
              refine ⟨648680085468170565567985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3459627122496909683029253 648680085468170565567985)
              ·
                refine ⟨486510064101127924175989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 648680085468170565567985 486510064101127924175989)
                ·
                  refine ⟨45610318509480742891499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 486510064101127924175989 45610318509480742891499)
                  ·
                    rfl

theorem cell22_399716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_399716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_399716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_399716 prefixEnd_399716 := by exact prefixLift 399716
  have htrace : WordTrace (prefixWord ++ tailWord_399716) baseStart_399716 baseEnd_399716 := by
    simpa [prefixWord, tailWord_399716, baseEnd_399716] using wordTrace_append hprefix tailTrace_399716
  have hstable : (prefixWord ++ tailWord_399716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399716).length < 2 ^ (prefixWord ++ tailWord_399716).sum := by decide
  have hdescent : baseEnd_399716 < baseStart_399716 := by decide
  rcases family_descends (prefixWord ++ tailWord_399716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399720 : List Nat := [2, 1, 4, 2, 2, 2, 1, 4, 1, 3]
def baseStart_399720 : Nat := 118140960795 + 399720 * 2 ^ 59
def prefixEnd_399720 : Nat := 4983230072969 + 3 ^ 40 * 399720 * 2
def baseEnd_399720 : Nat := 136832324810187551574485

theorem tailTrace_399720 : CollatzResearch.WordTrace tailWord_399720 prefixEnd_399720 136832324810187551574485 := by
  unfold tailWord_399720
  simp only [CollatzResearch.WordTrace]
  refine ⟨7289493055945090793058307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9719324074593454390744409 7289493055945090793058307)
  ·
    refine ⟨10934239583917636189587461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7289493055945090793058307 10934239583917636189587461)
    ·
      refine ⟨2050169921984556785547649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10934239583917636189587461 2050169921984556785547649)
      ·
        refine ⟨1537627441488417589160737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2050169921984556785547649 1537627441488417589160737)
        ·
          refine ⟨1153220581116313191870553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1537627441488417589160737 1153220581116313191870553)
          ·
            refine ⟨864915435837234893902915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1153220581116313191870553 864915435837234893902915)
            ·
              refine ⟨1297373153755852340854373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 864915435837234893902915 1297373153755852340854373)
              ·
                refine ⟨243257466329222313910195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1297373153755852340854373 243257466329222313910195)
                ·
                  refine ⟨364886199493833470865293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243257466329222313910195 364886199493833470865293)
                  ·
                    refine ⟨136832324810187551574485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 364886199493833470865293 136832324810187551574485)
                    ·
                      rfl

theorem cell22_399720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_399720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_399720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_399720 prefixEnd_399720 := by exact prefixLift 399720
  have htrace : WordTrace (prefixWord ++ tailWord_399720) baseStart_399720 baseEnd_399720 := by
    simpa [prefixWord, tailWord_399720, baseEnd_399720] using wordTrace_append hprefix tailTrace_399720
  have hstable : (prefixWord ++ tailWord_399720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399720).length < 2 ^ (prefixWord ++ tailWord_399720).sum := by decide
  have hdescent : baseEnd_399720 < baseStart_399720 := by decide
  rcases family_descends (prefixWord ++ tailWord_399720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399778 : List Nat := [3, 3, 1, 2, 1, 1, 1, 6, 4]
def baseStart_399778 : Nat := 118140960795 + 399778 * 2 ^ 59
def prefixEnd_399778 : Nat := 4983230072969 + 3 ^ 40 * 399778 * 2
def baseEnd_399778 : Nat := 45617393131831577874769

theorem tailTrace_399778 : CollatzResearch.WordTrace tailWord_399778 prefixEnd_399778 45617393131831577874769 := by
  unfold tailWord_399778
  simp only [CollatzResearch.WordTrace]
  refine ⟨3645275386420014372931997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9720734363786704994485325 3645275386420014372931997)
  ·
    refine ⟨1366978269907505389849499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3645275386420014372931997 1366978269907505389849499)
    ·
      refine ⟨2050467404861258084774249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1366978269907505389849499 2050467404861258084774249)
      ·
        refine ⟨1537850553645943563580687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2050467404861258084774249 1537850553645943563580687)
        ·
          refine ⟨2306775830468915345371031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1537850553645943563580687 2306775830468915345371031)
          ·
            refine ⟨3460163745703373018056547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2306775830468915345371031 3460163745703373018056547)
            ·
              refine ⟨5190245618555059527084821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3460163745703373018056547 5190245618555059527084821)
              ·
                refine ⟨243292763369768415332101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5190245618555059527084821 243292763369768415332101)
                ·
                  refine ⟨45617393131831577874769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 243292763369768415332101 45617393131831577874769)
                  ·
                    rfl

theorem cell22_399778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_399778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_399778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_399778 prefixEnd_399778 := by exact prefixLift 399778
  have htrace : WordTrace (prefixWord ++ tailWord_399778) baseStart_399778 baseEnd_399778 := by
    simpa [prefixWord, tailWord_399778, baseEnd_399778] using wordTrace_append hprefix tailTrace_399778
  have hstable : (prefixWord ++ tailWord_399778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399778).length < 2 ^ (prefixWord ++ tailWord_399778).sum := by decide
  have hdescent : baseEnd_399778 < baseStart_399778 := by decide
  rcases family_descends (prefixWord ++ tailWord_399778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399793 : List Nat := [1, 2, 2, 4, 1, 4, 1, 1, 1, 5]
def baseStart_399793 : Nat := 118140960795 + 399793 * 2 ^ 59
def prefixEnd_399793 : Nat := 4983230072969 + 3 ^ 40 * 399793 * 2
def baseEnd_399793 : Nat := 136857314202039694499261

theorem tailTrace_399793 : CollatzResearch.WordTrace tailWord_399793 prefixEnd_399793 136857314202039694499261 := by
  unfold tailWord_399793
  simp only [CollatzResearch.WordTrace]
  refine ⟨14581648640625715053524033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9721099093750476702349355 14581648640625715053524033)
  ·
    refine ⟨10936236480469286290143025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14581648640625715053524033 10936236480469286290143025)
    ·
      refine ⟨8202177360351964717607269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10936236480469286290143025 8202177360351964717607269)
      ·
        refine ⟨1537908255065993384551363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8202177360351964717607269 1537908255065993384551363)
        ·
          refine ⟨2306862382598990076827045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1537908255065993384551363 2306862382598990076827045)
          ·
            refine ⟨432536696737310639405071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2306862382598990076827045 432536696737310639405071)
            ·
              refine ⟨648805045105965959107607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432536696737310639405071 648805045105965959107607)
              ·
                refine ⟨973207567658948938661411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 648805045105965959107607 973207567658948938661411)
                ·
                  refine ⟨1459811351488423407992117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 973207567658948938661411 1459811351488423407992117)
                  ·
                    refine ⟨136857314202039694499261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1459811351488423407992117 136857314202039694499261)
                    ·
                      rfl

theorem cell22_399793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 5].length) (baseStart_399793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_399793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_399793 prefixEnd_399793 := by exact prefixLift 399793
  have htrace : WordTrace (prefixWord ++ tailWord_399793) baseStart_399793 baseEnd_399793 := by
    simpa [prefixWord, tailWord_399793, baseEnd_399793] using wordTrace_append hprefix tailTrace_399793
  have hstable : (prefixWord ++ tailWord_399793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399793).length < 2 ^ (prefixWord ++ tailWord_399793).sum := by decide
  have hdescent : baseEnd_399793 < baseStart_399793 := by decide
  rcases family_descends (prefixWord ++ tailWord_399793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399812 : List Nat := [2, 3, 3, 2, 2, 2, 1, 3, 4]
def baseStart_399812 : Nat := 118140960795 + 399812 * 2 ^ 59
def prefixEnd_399812 : Nat := 4983230072969 + 3 ^ 40 * 399812 * 2
def baseEnd_399812 : Nat := 45621272763443326091401

theorem tailTrace_399812 : CollatzResearch.WordTrace tailWord_399812 prefixEnd_399812 45621272763443326091401 := by
  unfold tailWord_399812
  simp only [CollatzResearch.WordTrace]
  refine ⟨7291170813778440649232845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9721561085037920865643793 7291170813778440649232845)
  ·
    refine ⟨2734189055166915243462317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7291170813778440649232845 2734189055166915243462317)
    ·
      refine ⟨1025320895687593216298369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2734189055166915243462317 1025320895687593216298369)
      ·
        refine ⟨768990671765694912223777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1025320895687593216298369 768990671765694912223777)
        ·
          refine ⟨576743003824271184167833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 768990671765694912223777 576743003824271184167833)
          ·
            refine ⟨432557252868203388125875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 576743003824271184167833 432557252868203388125875)
            ·
              refine ⟨648835879302305082188813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432557252868203388125875 648835879302305082188813)
              ·
                refine ⟨243313454738364405820805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 648835879302305082188813 243313454738364405820805)
                ·
                  refine ⟨45621272763443326091401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 243313454738364405820805 45621272763443326091401)
                  ·
                    rfl

theorem cell22_399812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_399812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_399812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_399812 prefixEnd_399812 := by exact prefixLift 399812
  have htrace : WordTrace (prefixWord ++ tailWord_399812) baseStart_399812 baseEnd_399812 := by
    simpa [prefixWord, tailWord_399812, baseEnd_399812] using wordTrace_append hprefix tailTrace_399812
  have hstable : (prefixWord ++ tailWord_399812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399812).length < 2 ^ (prefixWord ++ tailWord_399812).sum := by decide
  have hdescent : baseEnd_399812 < baseStart_399812 := by decide
  rcases family_descends (prefixWord ++ tailWord_399812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399819 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 1, 8]
def baseStart_399819 : Nat := 118140960795 + 399819 * 2 ^ 59
def prefixEnd_399819 : Nat := 4983230072969 + 3 ^ 40 * 399819 * 2
def baseEnd_399819 : Nat := 136866214533384293349181

theorem tailTrace_399819 : CollatzResearch.WordTrace tailWord_399819 prefixEnd_399819 136866214533384293349181 := by
  unfold tailWord_399819
  simp only [CollatzResearch.WordTrace]
  refine ⟨14582596938531521493970511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9721731292354347662647007 14582596938531521493970511)
  ·
    refine ⟨21873895407797282240955767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14582596938531521493970511 21873895407797282240955767)
    ·
      refine ⟨32810843111695923361433651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21873895407797282240955767 32810843111695923361433651)
      ·
        refine ⟨49216264667543885042150477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32810843111695923361433651 49216264667543885042150477)
        ·
          refine ⟨18456099250328956890806429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49216264667543885042150477 18456099250328956890806429)
          ·
            refine ⟨6921037218873358834052411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18456099250328956890806429 6921037218873358834052411)
            ·
              refine ⟨10381555828310038251078617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6921037218873358834052411 10381555828310038251078617)
              ·
                refine ⟨7786166871232528688308963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10381555828310038251078617 7786166871232528688308963)
                ·
                  refine ⟨11679250306848793032463445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7786166871232528688308963 11679250306848793032463445)
                  ·
                    refine ⟨136866214533384293349181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11679250306848793032463445 136866214533384293349181)
                    ·
                      rfl

theorem cell22_399819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 8].length) (baseStart_399819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_399819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_399819 prefixEnd_399819 := by exact prefixLift 399819
  have htrace : WordTrace (prefixWord ++ tailWord_399819) baseStart_399819 baseEnd_399819 := by
    simpa [prefixWord, tailWord_399819, baseEnd_399819] using wordTrace_append hprefix tailTrace_399819
  have hstable : (prefixWord ++ tailWord_399819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399819).length < 2 ^ (prefixWord ++ tailWord_399819).sum := by decide
  have hdescent : baseEnd_399819 < baseStart_399819 := by decide
  rcases family_descends (prefixWord ++ tailWord_399819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399851 : List Nat := [1, 1, 1, 1, 2, 3, 5, 3, 5]
def baseStart_399851 : Nat := 118140960795 + 399851 * 2 ^ 59
def prefixEnd_399851 : Nat := 4983230072969 + 3 ^ 40 * 399851 * 2
def baseEnd_399851 : Nat := 45625722929115625516361

theorem tailTrace_399851 : CollatzResearch.WordTrace tailWord_399851 prefixEnd_399851 45625722929115625516361 := by
  unfold tailWord_399851
  simp only [CollatzResearch.WordTrace]
  refine ⟨14583764074415590959135407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9722509382943727306090271 14583764074415590959135407)
  ·
    refine ⟨21875646111623386438703111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14583764074415590959135407 21875646111623386438703111)
    ·
      refine ⟨32813469167435079658054667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21875646111623386438703111 32813469167435079658054667)
      ·
        refine ⟨49220203751152619487082001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32813469167435079658054667 49220203751152619487082001)
        ·
          refine ⟨36915152813364464615311501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49220203751152619487082001 36915152813364464615311501)
          ·
            refine ⟨13843182305011674230741813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36915152813364464615311501 13843182305011674230741813)
            ·
              refine ⟨1297798341094844459132045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13843182305011674230741813 1297798341094844459132045)
              ·
                refine ⟨486674377910566672174517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1297798341094844459132045 486674377910566672174517)
                ·
                  refine ⟨45625722929115625516361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 486674377910566672174517 45625722929115625516361)
                  ·
                    rfl

theorem cell22_399851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 5].length) (baseStart_399851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_399851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_399851 prefixEnd_399851 := by exact prefixLift 399851
  have htrace : WordTrace (prefixWord ++ tailWord_399851) baseStart_399851 baseEnd_399851 := by
    simpa [prefixWord, tailWord_399851, baseEnd_399851] using wordTrace_append hprefix tailTrace_399851
  have hstable : (prefixWord ++ tailWord_399851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399851).length < 2 ^ (prefixWord ++ tailWord_399851).sum := by decide
  have hdescent : baseEnd_399851 < baseStart_399851 := by decide
  rcases family_descends (prefixWord ++ tailWord_399851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399928 : List Nat := [2, 1, 2, 1, 4, 1, 2, 2, 4, 3]
def baseStart_399928 : Nat := 118140960795 + 399928 * 2 ^ 59
def prefixEnd_399928 : Nat := 4983230072969 + 3 ^ 40 * 399928 * 2
def baseEnd_399928 : Nat := 136903527460944342373847

theorem tailTrace_399928 : CollatzResearch.WordTrace tailWord_399928 prefixEnd_399928 136903527460944342373847 := by
  unfold tailWord_399928
  simp only [CollatzResearch.WordTrace]
  refine ⟨7293286247568316554844219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9724381663424422073125625 7293286247568316554844219)
  ·
    refine ⟨10939929371352474832266329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7293286247568316554844219 10939929371352474832266329)
    ·
      refine ⟨8204947028514356124199747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10939929371352474832266329 8204947028514356124199747)
      ·
        refine ⟨12307420542771534186299621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8204947028514356124199747 12307420542771534186299621)
        ·
          refine ⟨2307641351769662659931179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12307420542771534186299621 2307641351769662659931179)
          ·
            refine ⟨3461462027654493989896769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2307641351769662659931179 3461462027654493989896769)
            ·
              refine ⟨2596096520740870492422577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3461462027654493989896769 2596096520740870492422577)
              ·
                refine ⟨1947072390555652869316933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2596096520740870492422577 1947072390555652869316933)
                ·
                  refine ⟨365076073229184912996925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1947072390555652869316933 365076073229184912996925)
                  ·
                    refine ⟨136903527460944342373847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 365076073229184912996925 136903527460944342373847)
                    ·
                      rfl

theorem cell22_399928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 4, 3].length) (baseStart_399928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_399928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_399928 prefixEnd_399928 := by exact prefixLift 399928
  have htrace : WordTrace (prefixWord ++ tailWord_399928) baseStart_399928 baseEnd_399928 := by
    simpa [prefixWord, tailWord_399928, baseEnd_399928] using wordTrace_append hprefix tailTrace_399928
  have hstable : (prefixWord ++ tailWord_399928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399928).length < 2 ^ (prefixWord ++ tailWord_399928).sum := by decide
  have hdescent : baseEnd_399928 < baseStart_399928 := by decide
  rcases family_descends (prefixWord ++ tailWord_399928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399930 : List Nat := [3, 1, 1, 1, 3, 4, 2, 3, 4]
def baseStart_399930 : Nat := 118140960795 + 399930 * 2 ^ 59
def prefixEnd_399930 : Nat := 4983230072969 + 3 ^ 40 * 399930 * 2
def baseEnd_399930 : Nat := 45634737367272334607947

theorem tailTrace_399930 : CollatzResearch.WordTrace tailWord_399930 prefixEnd_399930 45634737367272334607947 := by
  unfold tailWord_399930
  simp only [CollatzResearch.WordTrace]
  refine ⟨3646661360282346862815311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9724430294086258300840829 3646661360282346862815311)
  ·
    refine ⟨5469992040423520294222967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3646661360282346862815311 5469992040423520294222967)
    ·
      refine ⟨8204988060635280441334451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5469992040423520294222967 8204988060635280441334451)
      ·
        refine ⟨12307482090952920662001677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8204988060635280441334451 12307482090952920662001677)
        ·
          refine ⟨4615305784107345248250629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12307482090952920662001677 4615305784107345248250629)
          ·
            refine ⟨865369834520127234046993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4615305784107345248250629 865369834520127234046993)
            ·
              refine ⟨649027375890095425535245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 865369834520127234046993 649027375890095425535245)
              ·
                refine ⟨243385265958785784575717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 649027375890095425535245 243385265958785784575717)
                ·
                  refine ⟨45634737367272334607947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 243385265958785784575717 45634737367272334607947)
                  ·
                    rfl

theorem cell22_399930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3, 4].length) (baseStart_399930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_399930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_399930 prefixEnd_399930 := by exact prefixLift 399930
  have htrace : WordTrace (prefixWord ++ tailWord_399930) baseStart_399930 baseEnd_399930 := by
    simpa [prefixWord, tailWord_399930, baseEnd_399930] using wordTrace_append hprefix tailTrace_399930
  have hstable : (prefixWord ++ tailWord_399930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399930).length < 2 ^ (prefixWord ++ tailWord_399930).sum := by decide
  have hdescent : baseEnd_399930 < baseStart_399930 := by decide
  rcases family_descends (prefixWord ++ tailWord_399930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399932 : List Nat := [2, 2, 2, 2, 3, 3, 2, 1, 1, 4]
def baseStart_399932 : Nat := 118140960795 + 399932 * 2 ^ 59
def prefixEnd_399932 : Nat := 4983230072969 + 3 ^ 40 * 399932 * 2
def baseEnd_399932 : Nat := 136904896742689665273835

theorem tailTrace_399932 : CollatzResearch.WordTrace tailWord_399932 prefixEnd_399932 136904896742689665273835 := by
  unfold tailWord_399932
  simp only [CollatzResearch.WordTrace]
  refine ⟨7293359193561070896417025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9724478924748094528556033 7293359193561070896417025)
  ·
    refine ⟨5470019395170803172312769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7293359193561070896417025 5470019395170803172312769)
    ·
      refine ⟨4102514546378102379234577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5470019395170803172312769 4102514546378102379234577)
      ·
        refine ⟨3076885909783576784425933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4102514546378102379234577 3076885909783576784425933)
        ·
          refine ⟨1153832216168841294159725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3076885909783576784425933 1153832216168841294159725)
          ·
            refine ⟨432687081063315485309897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1153832216168841294159725 432687081063315485309897)
            ·
              refine ⟨324515310797486613982423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432687081063315485309897 324515310797486613982423)
              ·
                refine ⟨486772966196229920973635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324515310797486613982423 486772966196229920973635)
                ·
                  refine ⟨730159449294344881460453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 486772966196229920973635 730159449294344881460453)
                  ·
                    refine ⟨136904896742689665273835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 730159449294344881460453 136904896742689665273835)
                    ·
                      rfl

theorem cell22_399932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_399932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_399932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_399932 prefixEnd_399932 := by exact prefixLift 399932
  have htrace : WordTrace (prefixWord ++ tailWord_399932) baseStart_399932 baseEnd_399932 := by
    simpa [prefixWord, tailWord_399932, baseEnd_399932] using wordTrace_append hprefix tailTrace_399932
  have hstable : (prefixWord ++ tailWord_399932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399932).length < 2 ^ (prefixWord ++ tailWord_399932).sum := by decide
  have hdescent : baseEnd_399932 < baseStart_399932 := by decide
  rcases family_descends (prefixWord ++ tailWord_399932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399941 : List Nat := [1, 3, 1, 1, 1, 6, 9]
def baseStart_399941 : Nat := 118140960795 + 399941 * 2 ^ 59
def prefixEnd_399941 : Nat := 4983230072969 + 3 ^ 40 * 399941 * 2
def baseEnd_399941 : Nat := 5070665838022838585141

theorem tailTrace_399941 : CollatzResearch.WordTrace tailWord_399941 prefixEnd_399941 5070665838022838585141 := by
  unfold tailWord_399941
  simp only [CollatzResearch.WordTrace]
  refine ⟨14587046644089536329911677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9724697762726357553274451 14587046644089536329911677)
  ·
    refine ⟨5470142491533576123716879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14587046644089536329911677 5470142491533576123716879)
    ·
      refine ⟨8205213737300364185575319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5470142491533576123716879 8205213737300364185575319)
      ·
        refine ⟨12307820605950546278362979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8205213737300364185575319 12307820605950546278362979)
        ·
          refine ⟨18461730908925819417544469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12307820605950546278362979 18461730908925819417544469)
          ·
            refine ⟨865393636355897785197397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18461730908925819417544469 865393636355897785197397)
            ·
              refine ⟨5070665838022838585141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 865393636355897785197397 5070665838022838585141)
              ·
                rfl

theorem cell22_399941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 9].length) (baseStart_399941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_399941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_399941 prefixEnd_399941 := by exact prefixLift 399941
  have htrace : WordTrace (prefixWord ++ tailWord_399941) baseStart_399941 baseEnd_399941 := by
    simpa [prefixWord, tailWord_399941, baseEnd_399941] using wordTrace_append hprefix tailTrace_399941
  have hstable : (prefixWord ++ tailWord_399941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399941).length < 2 ^ (prefixWord ++ tailWord_399941).sum := by decide
  have hdescent : baseEnd_399941 < baseStart_399941 := by decide
  rcases family_descends (prefixWord ++ tailWord_399941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399966 : List Nat := [4, 4, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_399966 : Nat := 118140960795 + 399966 * 2 ^ 59
def prefixEnd_399966 : Nat := 4983230072969 + 3 ^ 40 * 399966 * 2
def baseEnd_399966 : Nat := 136916535637524909923731

theorem tailTrace_399966 : CollatzResearch.WordTrace tailWord_399966 prefixEnd_399966 136916535637524909923731 := by
  unfold tailWord_399966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1823494808624870699946469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9725305645999310399714501 1823494808624870699946469)
  ·
    refine ⟨341905276617163256239963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1823494808624870699946469 341905276617163256239963)
    ·
      refine ⟨512857914925744884359945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341905276617163256239963 512857914925744884359945)
      ·
        refine ⟨384643436194308663269959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 512857914925744884359945 384643436194308663269959)
        ·
          refine ⟨576965154291462994904939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384643436194308663269959 576965154291462994904939)
          ·
            refine ⟨865447731437194492357409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576965154291462994904939 865447731437194492357409)
            ·
              refine ⟨649085798577895869268057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 865447731437194492357409 649085798577895869268057)
              ·
                refine ⟨486814348933421901951043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 649085798577895869268057 486814348933421901951043)
                ·
                  refine ⟨730221523400132852926565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 486814348933421901951043 730221523400132852926565)
                  ·
                    refine ⟨136916535637524909923731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 730221523400132852926565 136916535637524909923731)
                    ·
                      rfl

theorem cell22_399966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_399966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_399966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_399966 prefixEnd_399966 := by exact prefixLift 399966
  have htrace : WordTrace (prefixWord ++ tailWord_399966) baseStart_399966 baseEnd_399966 := by
    simpa [prefixWord, tailWord_399966, baseEnd_399966] using wordTrace_append hprefix tailTrace_399966
  have hstable : (prefixWord ++ tailWord_399966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399966).length < 2 ^ (prefixWord ++ tailWord_399966).sum := by decide
  have hdescent : baseEnd_399966 < baseStart_399966 := by decide
  rcases family_descends (prefixWord ++ tailWord_399966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400016 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 1, 10]
def baseStart_400016 : Nat := 118140960795 + 400016 * 2 ^ 59
def prefixEnd_400016 : Nat := 4983230072969 + 3 ^ 40 * 400016 * 2
def baseEnd_400016 : Nat := 136933651659341446173577

theorem tailTrace_400016 : CollatzResearch.WordTrace tailWord_400016 prefixEnd_400016 136933651659341446173577 := by
  unfold tailWord_400016
  simp only [CollatzResearch.WordTrace]
  refine ⟨7294891059408912069445951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9726521412545216092594601 7294891059408912069445951)
  ·
    refine ⟨10942336589113368104168927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7294891059408912069445951 10942336589113368104168927)
    ·
      refine ⟨16413504883670052156253391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10942336589113368104168927 16413504883670052156253391)
      ·
        refine ⟨24620257325505078234380087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16413504883670052156253391 24620257325505078234380087)
        ·
          refine ⟨36930385988257617351570131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24620257325505078234380087 36930385988257617351570131)
          ·
            refine ⟨55395578982386426027355197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36930385988257617351570131 55395578982386426027355197)
            ·
              refine ⟨20773342118394909760258199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55395578982386426027355197 20773342118394909760258199)
              ·
                refine ⟨31160013177592364640387299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20773342118394909760258199 31160013177592364640387299)
                ·
                  refine ⟨46740019766388546960580949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31160013177592364640387299 46740019766388546960580949)
                  ·
                    refine ⟨136933651659341446173577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 46740019766388546960580949 136933651659341446173577)
                    ·
                      rfl

theorem cell22_400016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 10].length) (baseStart_400016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_400016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_400016 prefixEnd_400016 := by exact prefixLift 400016
  have htrace : WordTrace (prefixWord ++ tailWord_400016) baseStart_400016 baseEnd_400016 := by
    simpa [prefixWord, tailWord_400016, baseEnd_400016] using wordTrace_append hprefix tailTrace_400016
  have hstable : (prefixWord ++ tailWord_400016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400016).length < 2 ^ (prefixWord ++ tailWord_400016).sum := by decide
  have hdescent : baseEnd_400016 < baseStart_400016 := by decide
  rcases family_descends (prefixWord ++ tailWord_400016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400054 : List Nat := [5, 1, 3, 1, 2, 1, 2, 2, 5]
def baseStart_400054 : Nat := 118140960795 + 400054 * 2 ^ 59
def prefixEnd_400054 : Nat := 4983230072969 + 3 ^ 40 * 400054 * 2
def baseEnd_400054 : Nat := 45648886611974004574487

theorem tailTrace_400054 : CollatzResearch.WordTrace tailWord_400054 prefixEnd_400054 45648886611974004574487 := by
  unfold tailWord_400054
  simp only [CollatzResearch.WordTrace]
  refine ⟨911948005792509789298451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9727445395120104419183477 911948005792509789298451)
  ·
    refine ⟨1367922008688764683947677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 911948005792509789298451 1367922008688764683947677)
    ·
      refine ⟨512970753258286756480379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1367922008688764683947677 512970753258286756480379)
      ·
        refine ⟨769456129887430134720569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512970753258286756480379 769456129887430134720569)
        ·
          refine ⟨577092097415572601040427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 769456129887430134720569 577092097415572601040427)
          ·
            refine ⟨865638146123358901560641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577092097415572601040427 865638146123358901560641)
            ·
              refine ⟨649228609592519176170481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 865638146123358901560641 649228609592519176170481)
              ·
                refine ⟨486921457194389382127861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 649228609592519176170481 486921457194389382127861)
                ·
                  refine ⟨45648886611974004574487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 486921457194389382127861 45648886611974004574487)
                  ·
                    rfl

theorem cell22_400054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_400054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_400054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_400054 prefixEnd_400054 := by exact prefixLift 400054
  have htrace : WordTrace (prefixWord ++ tailWord_400054) baseStart_400054 baseEnd_400054 := by
    simpa [prefixWord, tailWord_400054, baseEnd_400054] using wordTrace_append hprefix tailTrace_400054
  have hstable : (prefixWord ++ tailWord_400054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400054).length < 2 ^ (prefixWord ++ tailWord_400054).sum := by decide
  have hdescent : baseEnd_400054 < baseStart_400054 := by decide
  rcases family_descends (prefixWord ++ tailWord_400054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400095 : List Nat := [1, 1, 2, 3, 2, 3, 3, 1, 2, 4]
def baseStart_400095 : Nat := 118140960795 + 400095 * 2 ^ 59
def prefixEnd_400095 : Nat := 4983230072969 + 3 ^ 40 * 400095 * 2
def baseEnd_400095 : Nat := 136960694973811573448335

theorem tailTrace_400095 : CollatzResearch.WordTrace tailWord_400095 prefixEnd_400095 136960694973811573448335 := by
  unfold tailWord_400095
  simp only [CollatzResearch.WordTrace]
  refine ⟨14592663485531620631017739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9728442323687747087345159 14592663485531620631017739)
  ·
    refine ⟨21888995228297430946526609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14592663485531620631017739 21888995228297430946526609)
    ·
      refine ⟨16416746421223073209894957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21888995228297430946526609 16416746421223073209894957)
      ·
        refine ⟨6156279907958652453710609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16416746421223073209894957 6156279907958652453710609)
        ·
          refine ⟨4617209930968989340282957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6156279907958652453710609 4617209930968989340282957)
          ·
            refine ⟨1731453724113371002606109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4617209930968989340282957 1731453724113371002606109)
            ·
              refine ⟨649295146542514125977291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1731453724113371002606109 649295146542514125977291)
              ·
                refine ⟨973942719813771188965937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649295146542514125977291 973942719813771188965937)
                ·
                  refine ⟨730457039860328391724453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 973942719813771188965937 730457039860328391724453)
                  ·
                    refine ⟨136960694973811573448335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 730457039860328391724453 136960694973811573448335)
                    ·
                      rfl

theorem cell22_400095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 4].length) (baseStart_400095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_400095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_400095 prefixEnd_400095 := by exact prefixLift 400095
  have htrace : WordTrace (prefixWord ++ tailWord_400095) baseStart_400095 baseEnd_400095 := by
    simpa [prefixWord, tailWord_400095, baseEnd_400095] using wordTrace_append hprefix tailTrace_400095
  have hstable : (prefixWord ++ tailWord_400095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400095).length < 2 ^ (prefixWord ++ tailWord_400095).sum := by decide
  have hdescent : baseEnd_400095 < baseStart_400095 := by decide
  rcases family_descends (prefixWord ++ tailWord_400095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400114 : List Nat := [3, 2, 1, 3, 1, 4, 1, 2, 2, 3]
def baseStart_400114 : Nat := 118140960795 + 400114 * 2 ^ 59
def prefixEnd_400114 : Nat := 4983230072969 + 3 ^ 40 * 400114 * 2
def baseEnd_400114 : Nat := 136967199062101857223277

theorem tailTrace_400114 : CollatzResearch.WordTrace tailWord_400114 prefixEnd_400114 136967199062101857223277 := by
  unfold tailWord_400114
  simp only [CollatzResearch.WordTrace]
  refine ⟨3648339118115696718989849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9728904314975191250639597 3648339118115696718989849)
  ·
    refine ⟨2736254338586772539242387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3648339118115696718989849 2736254338586772539242387)
    ·
      refine ⟨4104381507880158808863581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2736254338586772539242387 4104381507880158808863581)
      ·
        refine ⟨1539143065455059553323843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4104381507880158808863581 1539143065455059553323843)
        ·
          refine ⟨2308714598182589329985765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1539143065455059553323843 2308714598182589329985765)
          ·
            refine ⟨432883987159235499372331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2308714598182589329985765 432883987159235499372331)
            ·
              refine ⟨649325980738853249058497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432883987159235499372331 649325980738853249058497)
              ·
                refine ⟨486994485554139936793873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 649325980738853249058497 486994485554139936793873)
                ·
                  refine ⟨365245864165604952595405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486994485554139936793873 365245864165604952595405)
                  ·
                    refine ⟨136967199062101857223277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 365245864165604952595405 136967199062101857223277)
                    ·
                      rfl

theorem cell22_400114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_400114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_400114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_400114 prefixEnd_400114 := by exact prefixLift 400114
  have htrace : WordTrace (prefixWord ++ tailWord_400114) baseStart_400114 baseEnd_400114 := by
    simpa [prefixWord, tailWord_400114, baseEnd_400114] using wordTrace_append hprefix tailTrace_400114
  have hstable : (prefixWord ++ tailWord_400114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400114).length < 2 ^ (prefixWord ++ tailWord_400114).sum := by decide
  have hdescent : baseEnd_400114 < baseStart_400114 := by decide
  rcases family_descends (prefixWord ++ tailWord_400114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400153 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 4, 5]
def baseStart_400153 : Nat := 118140960795 + 400153 * 2 ^ 59
def prefixEnd_400153 : Nat := 4983230072969 + 3 ^ 40 * 400153 * 2
def baseEnd_400153 : Nat := 136980549559118755498157

theorem tailTrace_400153 : CollatzResearch.WordTrace tailWord_400153 prefixEnd_400153 136980549559118755498157 := by
  unfold tailWord_400153
  simp only [CollatzResearch.WordTrace]
  refine ⟨14594778919321496536629113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9729852612880997691086075 14594778919321496536629113)
  ·
    refine ⟨10946084189491122402471835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14594778919321496536629113 10946084189491122402471835)
    ·
      refine ⟨16419126284236683603707753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10946084189491122402471835 16419126284236683603707753)
      ·
        refine ⟨12314344713177512702780815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16419126284236683603707753 12314344713177512702780815)
        ·
          refine ⟨18471517069766269054171223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12314344713177512702780815 18471517069766269054171223)
          ·
            refine ⟨27707275604649403581256835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18471517069766269054171223 27707275604649403581256835)
            ·
              refine ⟨41560913406974105371885253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27707275604649403581256835 41560913406974105371885253)
              ·
                refine ⟨7792671263807644757228485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41560913406974105371885253 7792671263807644757228485)
                ·
                  refine ⟨1461125861963933391980341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7792671263807644757228485 1461125861963933391980341)
                  ·
                    refine ⟨136980549559118755498157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1461125861963933391980341 136980549559118755498157)
                    ·
                      rfl

theorem cell22_400153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 5].length) (baseStart_400153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_400153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_400153 prefixEnd_400153 := by exact prefixLift 400153
  have htrace : WordTrace (prefixWord ++ tailWord_400153) baseStart_400153 baseEnd_400153 := by
    simpa [prefixWord, tailWord_400153, baseEnd_400153] using wordTrace_append hprefix tailTrace_400153
  have hstable : (prefixWord ++ tailWord_400153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400153).length < 2 ^ (prefixWord ++ tailWord_400153).sum := by decide
  have hdescent : baseEnd_400153 < baseStart_400153 := by decide
  rcases family_descends (prefixWord ++ tailWord_400153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400159 : List Nat := [1, 1, 2, 4, 2, 2, 3, 3, 1, 3]
def baseStart_400159 : Nat := 118140960795 + 400159 * 2 ^ 59
def prefixEnd_400159 : Nat := 4983230072969 + 3 ^ 40 * 400159 * 2
def baseEnd_400159 : Nat := 136982603481736739848139

theorem tailTrace_400159 : CollatzResearch.WordTrace tailWord_400159 prefixEnd_400159 136982603481736739848139 := by
  unfold tailWord_400159
  simp only [CollatzResearch.WordTrace]
  refine ⟨14594997757299759561347531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9729998504866506374231687 14594997757299759561347531)
  ·
    refine ⟨21892496635949639342021297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14594997757299759561347531 21892496635949639342021297)
    ·
      refine ⟨16419372476962229506515973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21892496635949639342021297 16419372476962229506515973)
      ·
        refine ⟨3078632339430418032471745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16419372476962229506515973 3078632339430418032471745)
        ·
          refine ⟨2308974254572813524353809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3078632339430418032471745 2308974254572813524353809)
          ·
            refine ⟨1731730690929610143265357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2308974254572813524353809 1731730690929610143265357)
            ·
              refine ⟨649399009098603803724509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1731730690929610143265357 649399009098603803724509)
              ·
                refine ⟨243524628411976426396691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 649399009098603803724509 243524628411976426396691)
                ·
                  refine ⟨365286942617964639595037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243524628411976426396691 365286942617964639595037)
                  ·
                    refine ⟨136982603481736739848139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 365286942617964639595037 136982603481736739848139)
                    ·
                      rfl

theorem cell22_400159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3, 1, 3].length) (baseStart_400159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_400159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_400159 prefixEnd_400159 := by exact prefixLift 400159
  have htrace : WordTrace (prefixWord ++ tailWord_400159) baseStart_400159 baseEnd_400159 := by
    simpa [prefixWord, tailWord_400159, baseEnd_400159] using wordTrace_append hprefix tailTrace_400159
  have hstable : (prefixWord ++ tailWord_400159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400159).length < 2 ^ (prefixWord ++ tailWord_400159).sum := by decide
  have hdescent : baseEnd_400159 < baseStart_400159 := by decide
  rcases family_descends (prefixWord ++ tailWord_400159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400215 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 3, 5]
def baseStart_400215 : Nat := 118140960795 + 400215 * 2 ^ 59
def prefixEnd_400215 : Nat := 4983230072969 + 3 ^ 40 * 400215 * 2
def baseEnd_400215 : Nat := 137001773426171260447967

theorem tailTrace_400215 : CollatzResearch.WordTrace tailWord_400215 prefixEnd_400215 137001773426171260447967 := by
  unfold tailWord_400215
  simp only [CollatzResearch.WordTrace]
  refine ⟨14597040245096881125386099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9731360163397920750257399 14597040245096881125386099)
  ·
    refine ⟨21895560367645321688079149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14597040245096881125386099 21895560367645321688079149)
    ·
      refine ⟨8210835137866995633029681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21895560367645321688079149 8210835137866995633029681)
      ·
        refine ⟨6158126353400246724772261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8210835137866995633029681 6158126353400246724772261)
        ·
          refine ⟨1154648691262546260894799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6158126353400246724772261 1154648691262546260894799)
          ·
            refine ⟨1731973036893819391342199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154648691262546260894799 1731973036893819391342199)
            ·
              refine ⟨2597959555340729087013299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1731973036893819391342199 2597959555340729087013299)
              ·
                refine ⟨3896939333011093630519949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2597959555340729087013299 3896939333011093630519949)
                ·
                  refine ⟨1461352249879160111444981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3896939333011093630519949 1461352249879160111444981)
                  ·
                    refine ⟨137001773426171260447967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1461352249879160111444981 137001773426171260447967)
                    ·
                      rfl

theorem cell22_400215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_400215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_400215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_400215 prefixEnd_400215 := by exact prefixLift 400215
  have htrace : WordTrace (prefixWord ++ tailWord_400215) baseStart_400215 baseEnd_400215 := by
    simpa [prefixWord, tailWord_400215, baseEnd_400215] using wordTrace_append hprefix tailTrace_400215
  have hstable : (prefixWord ++ tailWord_400215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400215).length < 2 ^ (prefixWord ++ tailWord_400215).sum := by decide
  have hdescent : baseEnd_400215 < baseStart_400215 := by decide
  rcases family_descends (prefixWord ++ tailWord_400215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400264 : List Nat := [2, 1, 3, 3, 2, 3, 1, 1, 2, 4]
def baseStart_400264 : Nat := 118140960795 + 400264 * 2 ^ 59
def prefixEnd_400264 : Nat := 4983230072969 + 3 ^ 40 * 400264 * 2
def baseEnd_400264 : Nat := 137018547127551465972817

theorem tailTrace_400264 : CollatzResearch.WordTrace tailWord_400264 prefixEnd_400264 137018547127551465972817 := by
  unfold tailWord_400264
  simp only [CollatzResearch.WordTrace]
  refine ⟨7299413710959681246959923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9732551614612908329279897 7299413710959681246959923)
  ·
    refine ⟨10949120566439521870439885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7299413710959681246959923 10949120566439521870439885)
    ·
      refine ⟨4105920212414820701414957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10949120566439521870439885 4105920212414820701414957)
      ·
        refine ⟨1539720079655557763030609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4105920212414820701414957 1539720079655557763030609)
        ·
          refine ⟨1154790059741668322272957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1539720079655557763030609 1154790059741668322272957)
          ·
            refine ⟨433046272403125620852359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1154790059741668322272957 433046272403125620852359)
            ·
              refine ⟨649569408604688431278539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433046272403125620852359 649569408604688431278539)
              ·
                refine ⟨974354112907032646917809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649569408604688431278539 974354112907032646917809)
                ·
                  refine ⟨730765584680274485188357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 974354112907032646917809 730765584680274485188357)
                  ·
                    refine ⟨137018547127551465972817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 730765584680274485188357 137018547127551465972817)
                    ·
                      rfl

theorem cell22_400264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_400264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_400264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_400264 prefixEnd_400264 := by exact prefixLift 400264
  have htrace : WordTrace (prefixWord ++ tailWord_400264) baseStart_400264 baseEnd_400264 := by
    simpa [prefixWord, tailWord_400264, baseEnd_400264] using wordTrace_append hprefix tailTrace_400264
  have hstable : (prefixWord ++ tailWord_400264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400264).length < 2 ^ (prefixWord ++ tailWord_400264).sum := by decide
  have hdescent : baseEnd_400264 < baseStart_400264 := by decide
  rcases family_descends (prefixWord ++ tailWord_400264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400328 : List Nat := [2, 1, 3, 1, 5, 2, 1, 3, 1, 3]
def baseStart_400328 : Nat := 118140960795 + 400328 * 2 ^ 59
def prefixEnd_400328 : Nat := 4983230072969 + 3 ^ 40 * 400328 * 2
def baseEnd_400328 : Nat := 137040455635476632372621

theorem tailTrace_400328 : CollatzResearch.WordTrace tailWord_400328 prefixEnd_400328 137040455635476632372621 := by
  unfold tailWord_400328
  simp only [CollatzResearch.WordTrace]
  refine ⟨7300580846843750712124819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9734107795791667616166425 7300580846843750712124819)
  ·
    refine ⟨10950871270265626068187229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7300580846843750712124819 10950871270265626068187229)
    ·
      refine ⟨4106576726349609775570211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10950871270265626068187229 4106576726349609775570211)
      ·
        refine ⟨6159865089524414663355317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4106576726349609775570211 6159865089524414663355317)
        ·
          refine ⟨577487352142913874689561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6159865089524414663355317 577487352142913874689561)
          ·
            refine ⟨433115514107185406017171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 577487352142913874689561 433115514107185406017171)
            ·
              refine ⟨649673271160778109025757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433115514107185406017171 649673271160778109025757)
              ·
                refine ⟨243627476685291790884659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 649673271160778109025757 243627476685291790884659)
                ·
                  refine ⟨365441215027937686326989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243627476685291790884659 365441215027937686326989)
                  ·
                    refine ⟨137040455635476632372621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 365441215027937686326989 137040455635476632372621)
                    ·
                      rfl

theorem cell22_400328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_400328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_400328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_400328 prefixEnd_400328 := by exact prefixLift 400328
  have htrace : WordTrace (prefixWord ++ tailWord_400328) baseStart_400328 baseEnd_400328 := by
    simpa [prefixWord, tailWord_400328, baseEnd_400328] using wordTrace_append hprefix tailTrace_400328
  have hstable : (prefixWord ++ tailWord_400328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400328).length < 2 ^ (prefixWord ++ tailWord_400328).sum := by decide
  have hdescent : baseEnd_400328 < baseStart_400328 := by decide
  rcases family_descends (prefixWord ++ tailWord_400328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400337 : List Nat := [1, 2, 2, 1, 2, 1, 3, 5, 1, 4]
def baseStart_400337 : Nat := 118140960795 + 400337 * 2 ^ 59
def prefixEnd_400337 : Nat := 4983230072969 + 3 ^ 40 * 400337 * 2
def baseEnd_400337 : Nat := 137043536519403608897593

theorem tailTrace_400337 : CollatzResearch.WordTrace tailWord_400337 prefixEnd_400337 137043536519403608897593 := by
  unfold tailWord_400337
  simp only [CollatzResearch.WordTrace]
  refine ⟨14601489950654895961327265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9734326633769930640884843 14601489950654895961327265)
  ·
    refine ⟨10951117462991171970995449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14601489950654895961327265 10951117462991171970995449)
    ·
      refine ⟨8213338097243378978246587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10951117462991171970995449 8213338097243378978246587)
      ·
        refine ⟨12320007145865068467369881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8213338097243378978246587 12320007145865068467369881)
        ·
          refine ⟨9240005359398801350527411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12320007145865068467369881 9240005359398801350527411)
          ·
            refine ⟨13860008039098202025791117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9240005359398801350527411 13860008039098202025791117)
            ·
              refine ⟨5197503014661825759671669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13860008039098202025791117 5197503014661825759671669)
              ·
                refine ⟨487265907624546164969219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5197503014661825759671669 487265907624546164969219)
                ·
                  refine ⟨730898861436819247453829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 487265907624546164969219 730898861436819247453829)
                  ·
                    refine ⟨137043536519403608897593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 730898861436819247453829 137043536519403608897593)
                    ·
                      rfl

theorem cell22_400337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_400337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_400337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_400337 prefixEnd_400337 := by exact prefixLift 400337
  have htrace : WordTrace (prefixWord ++ tailWord_400337) baseStart_400337 baseEnd_400337 := by
    simpa [prefixWord, tailWord_400337, baseEnd_400337] using wordTrace_append hprefix tailTrace_400337
  have hstable : (prefixWord ++ tailWord_400337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400337).length < 2 ^ (prefixWord ++ tailWord_400337).sum := by decide
  have hdescent : baseEnd_400337 < baseStart_400337 := by decide
  rcases family_descends (prefixWord ++ tailWord_400337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400476 : List Nat := [2, 2, 4, 1, 1, 1, 5, 1, 5]
def baseStart_400476 : Nat := 118140960795 + 400476 * 2 ^ 59
def prefixEnd_400476 : Nat := 4983230072969 + 3 ^ 40 * 400476 * 2
def baseEnd_400476 : Nat := 45697039686684526557389

theorem tailTrace_400476 : CollatzResearch.WordTrace tailWord_400476 prefixEnd_400476 45697039686684526557389 := by
  unfold tailWord_400476
  simp only [CollatzResearch.WordTrace]
  refine ⟨7303279848575661350318641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9737706464767548467091521 7303279848575661350318641)
  ·
    refine ⟨5477459886431746012738981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7303279848575661350318641 5477459886431746012738981)
    ·
      refine ⟨1027023728705952377388559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5477459886431746012738981 1027023728705952377388559)
      ·
        refine ⟨1540535593058928566082839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1027023728705952377388559 1540535593058928566082839)
        ·
          refine ⟨2310803389588392849124259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1540535593058928566082839 2310803389588392849124259)
          ·
            refine ⟨3466205084382589273686389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2310803389588392849124259 3466205084382589273686389)
            ·
              refine ⟨324956726660867744408099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3466205084382589273686389 324956726660867744408099)
              ·
                refine ⟨487435089991301616612149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324956726660867744408099 487435089991301616612149)
                ·
                  refine ⟨45697039686684526557389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 487435089991301616612149 45697039686684526557389)
                  ·
                    rfl

theorem cell22_400476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 5].length) (baseStart_400476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_400476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_400476 prefixEnd_400476 := by exact prefixLift 400476
  have htrace : WordTrace (prefixWord ++ tailWord_400476) baseStart_400476 baseEnd_400476 := by
    simpa [prefixWord, tailWord_400476, baseEnd_400476] using wordTrace_append hprefix tailTrace_400476
  have hstable : (prefixWord ++ tailWord_400476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400476).length < 2 ^ (prefixWord ++ tailWord_400476).sum := by decide
  have hdescent : baseEnd_400476 < baseStart_400476 := by decide
  rcases family_descends (prefixWord ++ tailWord_400476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400489 : List Nat := [1, 2, 1, 1, 1, 6, 1, 4, 1, 4]
def baseStart_400489 : Nat := 118140960795 + 400489 * 2 ^ 59
def prefixEnd_400489 : Nat := 4983230072969 + 3 ^ 40 * 400489 * 2
def baseEnd_400489 : Nat := 137095569225725879097127

theorem tailTrace_400489 : CollatzResearch.WordTrace tailWord_400489 prefixEnd_400489 137095569225725879097127 := by
  unfold tailWord_400489
  simp only [CollatzResearch.WordTrace]
  refine ⟨14607033846104225920860521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9738022564069483947240347 14607033846104225920860521)
  ·
    refine ⟨10955275384578169440645391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14607033846104225920860521 10955275384578169440645391)
    ·
      refine ⟨16432913076867254160968087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10955275384578169440645391 16432913076867254160968087)
      ·
        refine ⟨24649369615300881241452131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16432913076867254160968087 24649369615300881241452131)
        ·
          refine ⟨36974054422951321862178197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24649369615300881241452131 36974054422951321862178197)
          ·
            refine ⟨1733158801075843212289603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 36974054422951321862178197 1733158801075843212289603)
            ·
              refine ⟨2599738201613764818434405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1733158801075843212289603 2599738201613764818434405)
              ·
                refine ⟨487450912802580903456451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2599738201613764818434405 487450912802580903456451)
                ·
                  refine ⟨731176369203871355184677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 487450912802580903456451 731176369203871355184677)
                  ·
                    refine ⟨137095569225725879097127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 731176369203871355184677 137095569225725879097127)
                    ·
                      rfl

theorem cell22_400489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 4].length) (baseStart_400489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_400489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_400489 prefixEnd_400489 := by exact prefixLift 400489
  have htrace : WordTrace (prefixWord ++ tailWord_400489) baseStart_400489 baseEnd_400489 := by
    simpa [prefixWord, tailWord_400489, baseEnd_400489] using wordTrace_append hprefix tailTrace_400489
  have hstable : (prefixWord ++ tailWord_400489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400489).length < 2 ^ (prefixWord ++ tailWord_400489).sum := by decide
  have hdescent : baseEnd_400489 < baseStart_400489 := by decide
  rcases family_descends (prefixWord ++ tailWord_400489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400547 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 2, 7]
def baseStart_400547 : Nat := 118140960795 + 400547 * 2 ^ 59
def prefixEnd_400547 : Nat := 4983230072969 + 3 ^ 40 * 400547 * 2
def baseEnd_400547 : Nat := 137115423811033061146949

theorem tailTrace_400547 : CollatzResearch.WordTrace tailWord_400547 prefixEnd_400547 137115423811033061146949 := by
  unfold tailWord_400547
  simp only [CollatzResearch.WordTrace]
  refine ⟨14609149279894101826471895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9739432853262734550981263 14609149279894101826471895)
  ·
    refine ⟨21913723919841152739707843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14609149279894101826471895 21913723919841152739707843)
    ·
      refine ⟨32870585879761729109561765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21913723919841152739707843 32870585879761729109561765)
      ·
        refine ⟨6163234852455324208042831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32870585879761729109561765 6163234852455324208042831)
        ·
          refine ⟨9244852278682986312064247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6163234852455324208042831 9244852278682986312064247)
          ·
            refine ⟨13867278418024479468096371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9244852278682986312064247 13867278418024479468096371)
            ·
              refine ⟨20800917627036719202144557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13867278418024479468096371 20800917627036719202144557)
              ·
                refine ⟨7800344110138769700804209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20800917627036719202144557 7800344110138769700804209)
                ·
                  refine ⟨5850258082604077275603157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7800344110138769700804209 5850258082604077275603157)
                  ·
                    refine ⟨137115423811033061146949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5850258082604077275603157 137115423811033061146949)
                    ·
                      rfl

theorem cell22_400547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 7].length) (baseStart_400547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_400547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_400547 prefixEnd_400547 := by exact prefixLift 400547
  have htrace : WordTrace (prefixWord ++ tailWord_400547) baseStart_400547 baseEnd_400547 := by
    simpa [prefixWord, tailWord_400547, baseEnd_400547] using wordTrace_append hprefix tailTrace_400547
  have hstable : (prefixWord ++ tailWord_400547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400547).length < 2 ^ (prefixWord ++ tailWord_400547).sum := by decide
  have hdescent : baseEnd_400547 < baseStart_400547 := by decide
  rcases family_descends (prefixWord ++ tailWord_400547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400551 : List Nat := [1, 1, 6, 2, 1, 1, 1, 3, 2, 4]
def baseStart_400551 : Nat := 118140960795 + 400551 * 2 ^ 59
def prefixEnd_400551 : Nat := 4983230072969 + 3 ^ 40 * 400551 * 2
def baseEnd_400551 : Nat := 137116793092778384046937

theorem tailTrace_400551 : CollatzResearch.WordTrace tailWord_400551 prefixEnd_400551 137116793092778384046937 := by
  unfold tailWord_400551
  simp only [CollatzResearch.WordTrace]
  refine ⟨14609295171879610509617507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9739530114586407006411671 14609295171879610509617507)
  ·
    refine ⟨21913942757819415764426261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14609295171879610509617507 21913942757819415764426261)
    ·
      refine ⟨1027216066772785113957481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21913942757819415764426261 1027216066772785113957481)
      ·
        refine ⟨770412050079588835468111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1027216066772785113957481 770412050079588835468111)
        ·
          refine ⟨1155618075119383253202167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 770412050079588835468111 1155618075119383253202167)
          ·
            refine ⟨1733427112679074879803251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1155618075119383253202167 1733427112679074879803251)
            ·
              refine ⟨2600140669018612319704877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1733427112679074879803251 2600140669018612319704877)
              ·
                refine ⟨975052750881979619889329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2600140669018612319704877 975052750881979619889329)
                ·
                  refine ⟨731289563161484714916997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 975052750881979619889329 731289563161484714916997)
                  ·
                    refine ⟨137116793092778384046937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 731289563161484714916997 137116793092778384046937)
                    ·
                      rfl

theorem cell22_400551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_400551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_400551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_400551 prefixEnd_400551 := by exact prefixLift 400551
  have htrace : WordTrace (prefixWord ++ tailWord_400551) baseStart_400551 baseEnd_400551 := by
    simpa [prefixWord, tailWord_400551, baseEnd_400551] using wordTrace_append hprefix tailTrace_400551
  have hstable : (prefixWord ++ tailWord_400551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400551).length < 2 ^ (prefixWord ++ tailWord_400551).sum := by decide
  have hdescent : baseEnd_400551 < baseStart_400551 := by decide
  rcases family_descends (prefixWord ++ tailWord_400551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400566 : List Nat := [5, 1, 3, 2, 11]
def baseStart_400566 : Nat := 118140960795 + 400566 * 2 ^ 59
def prefixEnd_400566 : Nat := 4983230072969 + 3 ^ 40 * 400566 * 2
def baseEnd_400566 : Nat := 564287769133017880337

theorem tailTrace_400566 : CollatzResearch.WordTrace tailWord_400566 prefixEnd_400566 564287769133017880337 := by
  unfold tailWord_400566
  simp only [CollatzResearch.WordTrace]
  refine ⟨913115141676579254463347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9739894844550178714275701 913115141676579254463347)
  ·
    refine ⟨1369672712514868881695021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 913115141676579254463347 1369672712514868881695021)
    ·
      refine ⟨513627267193075830635633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1369672712514868881695021 513627267193075830635633)
      ·
        refine ⟨385220450394806872976725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 513627267193075830635633 385220450394806872976725)
        ·
          refine ⟨564287769133017880337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 385220450394806872976725 564287769133017880337)
          ·
            rfl

theorem cell22_400566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 11].length) (baseStart_400566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_400566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_400566 prefixEnd_400566 := by exact prefixLift 400566
  have htrace : WordTrace (prefixWord ++ tailWord_400566) baseStart_400566 baseEnd_400566 := by
    simpa [prefixWord, tailWord_400566, baseEnd_400566] using wordTrace_append hprefix tailTrace_400566
  have hstable : (prefixWord ++ tailWord_400566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400566).length < 2 ^ (prefixWord ++ tailWord_400566).sum := by decide
  have hdescent : baseEnd_400566 < baseStart_400566 := by decide
  rcases family_descends (prefixWord ++ tailWord_400566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400639 : List Nat := [1, 1, 2, 2, 1, 5, 1, 3, 6]
def baseStart_400639 : Nat := 118140960795 + 400639 * 2 ^ 59
def prefixEnd_400639 : Nat := 4983230072969 + 3 ^ 40 * 400639 * 2
def baseEnd_400639 : Nat := 45715639097058495948889

theorem tailTrace_400639 : CollatzResearch.WordTrace tailWord_400639 prefixEnd_400639 45715639097058495948889 := by
  unfold tailWord_400639
  simp only [CollatzResearch.WordTrace]
  refine ⟨14612504795560801538820971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9741669863707201025880647 14612504795560801538820971)
  ·
    refine ⟨21918757193341202308231457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14612504795560801538820971 21918757193341202308231457)
    ·
      refine ⟨16439067895005901731173593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21918757193341202308231457 16439067895005901731173593)
      ·
        refine ⟨12329300921254426298380195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16439067895005901731173593 12329300921254426298380195)
        ·
          refine ⟨18493951381881639447570293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12329300921254426298380195 18493951381881639447570293)
          ·
            refine ⟨1733807942051403698209715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18493951381881639447570293 1733807942051403698209715)
            ·
              refine ⟨2600711913077105547314573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1733807942051403698209715 2600711913077105547314573)
              ·
                refine ⟨975266967403914580242965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2600711913077105547314573 975266967403914580242965)
                ·
                  refine ⟨45715639097058495948889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 975266967403914580242965 45715639097058495948889)
                  ·
                    rfl

theorem cell22_400639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 6].length) (baseStart_400639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_400639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_400639 prefixEnd_400639 := by exact prefixLift 400639
  have htrace : WordTrace (prefixWord ++ tailWord_400639) baseStart_400639 baseEnd_400639 := by
    simpa [prefixWord, tailWord_400639, baseEnd_400639] using wordTrace_append hprefix tailTrace_400639
  have hstable : (prefixWord ++ tailWord_400639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400639).length < 2 ^ (prefixWord ++ tailWord_400639).sum := by decide
  have hdescent : baseEnd_400639 < baseStart_400639 := by decide
  rcases family_descends (prefixWord ++ tailWord_400639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400690 : List Nat := [3, 2, 1, 1, 4, 2, 3, 2, 4]
def baseStart_400690 : Nat := 118140960795 + 400690 * 2 ^ 59
def prefixEnd_400690 : Nat := 4983230072969 + 3 ^ 40 * 400690 * 2
def baseEnd_400690 : Nat := 45721458544476118273837

theorem tailTrace_400690 : CollatzResearch.WordTrace tailWord_400690 prefixEnd_400690 45721458544476118273837 := by
  unfold tailWord_400690
  simp only [CollatzResearch.WordTrace]
  refine ⟨3653591229594009312231881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9742909945584024832618349 3653591229594009312231881)
  ·
    refine ⟨2740193422195506984173911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3653591229594009312231881 2740193422195506984173911)
    ·
      refine ⟨4110290133293260476260867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2740193422195506984173911 4110290133293260476260867)
      ·
        refine ⟨6165435199939890714391301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4110290133293260476260867 6165435199939890714391301)
        ·
          refine ⟨1156019099988729508948369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6165435199939890714391301 1156019099988729508948369)
          ·
            refine ⟨867014324991547131711277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1156019099988729508948369 867014324991547131711277)
            ·
              refine ⟨325130371871830174391729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 867014324991547131711277 325130371871830174391729)
              ·
                refine ⟨243847778903872630793797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 325130371871830174391729 243847778903872630793797)
                ·
                  refine ⟨45721458544476118273837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 243847778903872630793797 45721458544476118273837)
                  ·
                    rfl

theorem cell22_400690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_400690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_400690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_400690 prefixEnd_400690 := by exact prefixLift 400690
  have htrace : WordTrace (prefixWord ++ tailWord_400690) baseStart_400690 baseEnd_400690 := by
    simpa [prefixWord, tailWord_400690, baseEnd_400690] using wordTrace_append hprefix tailTrace_400690
  have hstable : (prefixWord ++ tailWord_400690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400690).length < 2 ^ (prefixWord ++ tailWord_400690).sum := by decide
  have hdescent : baseEnd_400690 < baseStart_400690 := by decide
  rcases family_descends (prefixWord ++ tailWord_400690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400705 : List Nat := [1, 2, 5, 2, 1, 2, 1, 3, 2, 3]
def baseStart_400705 : Nat := 118140960795 + 400705 * 2 ^ 59
def prefixEnd_400705 : Nat := 4983230072969 + 3 ^ 40 * 400705 * 2
def baseEnd_400705 : Nat := 137169510439973315696465

theorem tailTrace_400705 : CollatzResearch.WordTrace tailWord_400705 prefixEnd_400705 137169510439973315696465 := by
  unfold tailWord_400705
  simp only [CollatzResearch.WordTrace]
  refine ⟨14614912013321694810723569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9743274675547796540482379 14614912013321694810723569)
  ·
    refine ⟨10961184009991271108042677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14614912013321694810723569 10961184009991271108042677)
    ·
      refine ⟨1027611000936681666379001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10961184009991271108042677 1027611000936681666379001)
      ·
        refine ⟨770708250702511249784251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1027611000936681666379001 770708250702511249784251)
        ·
          refine ⟨1156062376053766874676377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 770708250702511249784251 1156062376053766874676377)
          ·
            refine ⟨867046782040325156007283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1156062376053766874676377 867046782040325156007283)
            ·
              refine ⟨1300570173060487734010925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 867046782040325156007283 1300570173060487734010925)
              ·
                refine ⟨487713814897682900254097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1300570173060487734010925 487713814897682900254097)
                ·
                  refine ⟨365785361173262175190573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 487713814897682900254097 365785361173262175190573)
                  ·
                    refine ⟨137169510439973315696465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 365785361173262175190573 137169510439973315696465)
                    ·
                      rfl

theorem cell22_400705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_400705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_400705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_400705 prefixEnd_400705 := by exact prefixLift 400705
  have htrace : WordTrace (prefixWord ++ tailWord_400705) baseStart_400705 baseEnd_400705 := by
    simpa [prefixWord, tailWord_400705, baseEnd_400705] using wordTrace_append hprefix tailTrace_400705
  have hstable : (prefixWord ++ tailWord_400705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400705).length < 2 ^ (prefixWord ++ tailWord_400705).sum := by decide
  have hdescent : baseEnd_400705 < baseStart_400705 := by decide
  rcases family_descends (prefixWord ++ tailWord_400705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400726 : List Nat := [5, 2, 3, 1, 1, 1, 3, 1, 1, 4]
def baseStart_400726 : Nat := 118140960795 + 400726 * 2 ^ 59
def prefixEnd_400726 : Nat := 4983230072969 + 3 ^ 40 * 400726 * 2
def baseEnd_400726 : Nat := 137176699169136260921401

theorem tailTrace_400726 : CollatzResearch.WordTrace tailWord_400726 prefixEnd_400726 137176699169136260921401 := by
  unfold tailWord_400726
  simp only [CollatzResearch.WordTrace]
  refine ⟨913479871640350962327377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9743785297497076931492021 913479871640350962327377)
  ·
    refine ⟨685109903730263221745533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 913479871640350962327377 685109903730263221745533)
    ·
      refine ⟨256916213898848708154575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 685109903730263221745533 256916213898848708154575)
      ·
        refine ⟨385374320848273062231863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256916213898848708154575 385374320848273062231863)
        ·
          refine ⟨578061481272409593347795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385374320848273062231863 578061481272409593347795)
          ·
            refine ⟨867092221908614390021693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578061481272409593347795 867092221908614390021693)
            ·
              refine ⟨325159583215730396258135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 867092221908614390021693 325159583215730396258135)
              ·
                refine ⟨487739374823595594387203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325159583215730396258135 487739374823595594387203)
                ·
                  refine ⟨731609062235393391580805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 487739374823595594387203 731609062235393391580805)
                  ·
                    refine ⟨137176699169136260921401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 731609062235393391580805 137176699169136260921401)
                    ·
                      rfl

theorem cell22_400726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_400726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_400726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_400726 prefixEnd_400726 := by exact prefixLift 400726
  have htrace : WordTrace (prefixWord ++ tailWord_400726) baseStart_400726 baseEnd_400726 := by
    simpa [prefixWord, tailWord_400726, baseEnd_400726] using wordTrace_append hprefix tailTrace_400726
  have hstable : (prefixWord ++ tailWord_400726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400726).length < 2 ^ (prefixWord ++ tailWord_400726).sum := by decide
  have hdescent : baseEnd_400726 < baseStart_400726 := by decide
  rcases family_descends (prefixWord ++ tailWord_400726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400729 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 9]
def baseStart_400729 : Nat := 118140960795 + 400729 * 2 ^ 59
def prefixEnd_400729 : Nat := 4983230072969 + 3 ^ 40 * 400729 * 2
def baseEnd_400729 : Nat := 45725908710148417698797

theorem tailTrace_400729 : CollatzResearch.WordTrace tailWord_400729 prefixEnd_400729 45725908710148417698797 := by
  unfold tailWord_400729
  simp only [CollatzResearch.WordTrace]
  refine ⟨14615787365234746909597241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9743858243489831273064827 14615787365234746909597241)
  ·
    refine ⟨10961840523926060182197931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14615787365234746909597241 10961840523926060182197931)
    ·
      refine ⟨16442760785889090273296897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10961840523926060182197931 16442760785889090273296897)
      ·
        refine ⟨12332070589416817704972673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16442760785889090273296897 12332070589416817704972673)
        ·
          refine ⟨9249052942062613278729505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12332070589416817704972673 9249052942062613278729505)
          ·
            refine ⟨6936789706546959959047129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9249052942062613278729505 6936789706546959959047129)
            ·
              refine ⟨5202592279910219969285347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6936789706546959959047129 5202592279910219969285347)
              ·
                refine ⟨7803888419865329953928021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5202592279910219969285347 7803888419865329953928021)
                ·
                  refine ⟨45725908710148417698797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7803888419865329953928021 45725908710148417698797)
                  ·
                    rfl

theorem cell22_400729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 9].length) (baseStart_400729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_400729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_400729 prefixEnd_400729 := by exact prefixLift 400729
  have htrace : WordTrace (prefixWord ++ tailWord_400729) baseStart_400729 baseEnd_400729 := by
    simpa [prefixWord, tailWord_400729, baseEnd_400729] using wordTrace_append hprefix tailTrace_400729
  have hstable : (prefixWord ++ tailWord_400729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400729).length < 2 ^ (prefixWord ++ tailWord_400729).sum := by decide
  have hdescent : baseEnd_400729 < baseStart_400729 := by decide
  rcases family_descends (prefixWord ++ tailWord_400729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400793 : List Nat := [1, 2, 1, 2, 1, 6, 1, 3, 1, 4]
def baseStart_400793 : Nat := 118140960795 + 400793 * 2 ^ 59
def prefixEnd_400793 : Nat := 4983230072969 + 3 ^ 40 * 400793 * 2
def baseEnd_400793 : Nat := 137199634638370419496195

theorem tailTrace_400793 : CollatzResearch.WordTrace tailWord_400793 prefixEnd_400793 137199634638370419496195 := by
  unfold tailWord_400793
  simp only [CollatzResearch.WordTrace]
  refine ⟨14618121637002885839927033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9745414424668590559951355 14618121637002885839927033)
  ·
    refine ⟨10963591227752164379945275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14618121637002885839927033 10963591227752164379945275)
    ·
      refine ⟨16445386841628246569917913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10963591227752164379945275 16445386841628246569917913)
      ·
        refine ⟨12334040131221184927438435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16445386841628246569917913 12334040131221184927438435)
        ·
          refine ⟨18501060196831777391157653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12334040131221184927438435 18501060196831777391157653)
          ·
            refine ⟨867237196726489565210515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18501060196831777391157653 867237196726489565210515)
            ·
              refine ⟨1300855795089734347815773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 867237196726489565210515 1300855795089734347815773)
              ·
                refine ⟨487820923158650380430915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1300855795089734347815773 487820923158650380430915)
                ·
                  refine ⟨731731384737975570646373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 487820923158650380430915 731731384737975570646373)
                  ·
                    refine ⟨137199634638370419496195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 731731384737975570646373 137199634638370419496195)
                    ·
                      rfl

theorem cell22_400793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 4].length) (baseStart_400793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_400793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_400793 prefixEnd_400793 := by exact prefixLift 400793
  have htrace : WordTrace (prefixWord ++ tailWord_400793) baseStart_400793 baseEnd_400793 := by
    simpa [prefixWord, tailWord_400793, baseEnd_400793] using wordTrace_append hprefix tailTrace_400793
  have hstable : (prefixWord ++ tailWord_400793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400793).length < 2 ^ (prefixWord ++ tailWord_400793).sum := by decide
  have hdescent : baseEnd_400793 < baseStart_400793 := by decide
  rcases family_descends (prefixWord ++ tailWord_400793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400874 : List Nat := [3, 1, 3, 1, 4, 2, 2, 1, 2, 3]
def baseStart_400874 : Nat := 118140960795 + 400874 * 2 ^ 59
def prefixEnd_400874 : Nat := 4983230072969 + 3 ^ 40 * 400874 * 2
def baseEnd_400874 : Nat := 137227362593713208220947

theorem tailTrace_400874 : CollatzResearch.WordTrace tailWord_400874 prefixEnd_400874 137227362593713208220947 := by
  unfold tailWord_400874
  simp only [CollatzResearch.WordTrace]
  refine ⟨3655268987427359168406419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9747383966472957782417117 3655268987427359168406419)
  ·
    refine ⟨5482903481141038752609629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3655268987427359168406419 5482903481141038752609629)
    ·
      refine ⟨2056088805427889532228611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5482903481141038752609629 2056088805427889532228611)
      ·
        refine ⟨3084133208141834298342917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2056088805427889532228611 3084133208141834298342917)
        ·
          refine ⟨578274976526593930939297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3084133208141834298342917 578274976526593930939297)
          ·
            refine ⟨433706232394945448204473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 578274976526593930939297 433706232394945448204473)
            ·
              refine ⟨325279674296209086153355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 433706232394945448204473 325279674296209086153355)
              ·
                refine ⟨487919511444313629230033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325279674296209086153355 487919511444313629230033)
                ·
                  refine ⟨365939633583235221922525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 487919511444313629230033 365939633583235221922525)
                  ·
                    refine ⟨137227362593713208220947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 365939633583235221922525 137227362593713208220947)
                    ·
                      rfl

theorem cell22_400874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_400874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_400874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_400874 prefixEnd_400874 := by exact prefixLift 400874
  have htrace : WordTrace (prefixWord ++ tailWord_400874) baseStart_400874 baseEnd_400874 := by
    simpa [prefixWord, tailWord_400874, baseEnd_400874] using wordTrace_append hprefix tailTrace_400874
  have hstable : (prefixWord ++ tailWord_400874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400874).length < 2 ^ (prefixWord ++ tailWord_400874).sum := by decide
  have hdescent : baseEnd_400874 < baseStart_400874 := by decide
  rcases family_descends (prefixWord ++ tailWord_400874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400966 : List Nat := [6, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_400966 : Nat := 118140960795 + 400966 * 2 ^ 59
def prefixEnd_400966 : Nat := 4983230072969 + 3 ^ 40 * 400966 * 2
def baseEnd_400966 : Nat := 45752952024618544973555

theorem tailTrace_400966 : CollatzResearch.WordTrace tailWord_400966 prefixEnd_400966 45752952024618544973555 := by
  unfold tailWord_400966
  simp only [CollatzResearch.WordTrace]
  refine ⟨457013483293004262061711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9749620976917424257316501 457013483293004262061711)
  ·
    refine ⟨685520224939506393092567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 457013483293004262061711 685520224939506393092567)
    ·
      refine ⟨1028280337409259589638851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 685520224939506393092567 1028280337409259589638851)
      ·
        refine ⟨1542420506113889384458277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1028280337409259589638851 1542420506113889384458277)
        ·
          refine ⟨289203844896354259585927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1542420506113889384458277 289203844896354259585927)
          ·
            refine ⟨433805767344531389378891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289203844896354259585927 433805767344531389378891)
            ·
              refine ⟨650708651016797084068337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433805767344531389378891 650708651016797084068337)
              ·
                refine ⟨488031488262597813051253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 650708651016797084068337 488031488262597813051253)
                ·
                  refine ⟨45752952024618544973555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 488031488262597813051253 45752952024618544973555)
                  ·
                    rfl

theorem cell22_400966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_400966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_400966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_400966 prefixEnd_400966 := by exact prefixLift 400966
  have htrace : WordTrace (prefixWord ++ tailWord_400966) baseStart_400966 baseEnd_400966 := by
    simpa [prefixWord, tailWord_400966, baseEnd_400966] using wordTrace_append hprefix tailTrace_400966
  have hstable : (prefixWord ++ tailWord_400966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400966).length < 2 ^ (prefixWord ++ tailWord_400966).sum := by decide
  have hdescent : baseEnd_400966 < baseStart_400966 := by decide
  rcases family_descends (prefixWord ++ tailWord_400966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401005 : List Nat := [1, 5, 1, 1, 4, 1, 1, 8]
def baseStart_401005 : Nat := 118140960795 + 401005 * 2 ^ 59
def prefixEnd_401005 : Nat := 4983230072969 + 3 ^ 40 * 401005 * 2
def baseEnd_401005 : Nat := 15252467396763614799505

theorem tailTrace_401005 : CollatzResearch.WordTrace tailWord_401005 prefixEnd_401005 15252467396763614799505 := by
  unfold tailWord_401005
  simp only [CollatzResearch.WordTrace]
  refine ⟨14625853912234846046644469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9750569274823230697762979 14625853912234846046644469)
  ·
    refine ⟨1371173804272016816872919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14625853912234846046644469 1371173804272016816872919)
    ·
      refine ⟨2056760706408025225309379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1371173804272016816872919 2056760706408025225309379)
      ·
        refine ⟨3085141059612037837964069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2056760706408025225309379 3085141059612037837964069)
        ·
          refine ⟨578463948677257094618263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3085141059612037837964069 578463948677257094618263)
          ·
            refine ⟨867695923015885641927395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578463948677257094618263 867695923015885641927395)
            ·
              refine ⟨1301543884523828462891093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 867695923015885641927395 1301543884523828462891093)
              ·
                refine ⟨15252467396763614799505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1301543884523828462891093 15252467396763614799505)
                ·
                  rfl

theorem cell22_401005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 8].length) (baseStart_401005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401005 prefixEnd_401005 := by exact prefixLift 401005
  have htrace : WordTrace (prefixWord ++ tailWord_401005) baseStart_401005 baseEnd_401005 := by
    simpa [prefixWord, tailWord_401005, baseEnd_401005] using wordTrace_append hprefix tailTrace_401005
  have hstable : (prefixWord ++ tailWord_401005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401005).length < 2 ^ (prefixWord ++ tailWord_401005).sum := by decide
  have hdescent : baseEnd_401005 < baseStart_401005 := by decide
  rcases family_descends (prefixWord ++ tailWord_401005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401033 : List Nat := [1, 2, 1, 1, 4, 1, 4, 1, 7]
def baseStart_401033 : Nat := 118140960795 + 401033 * 2 ^ 59
def prefixEnd_401033 : Nat := 4983230072969 + 3 ^ 40 * 401033 * 2
def baseEnd_401033 : Nat := 45760597181029931165153

theorem tailTrace_401033 : CollatzResearch.WordTrace tailWord_401033 prefixEnd_401033 45760597181029931165153 := by
  unfold tailWord_401033
  simp only [CollatzResearch.WordTrace]
  refine ⟨14626875156133406828663753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9751250104088937885775835 14626875156133406828663753)
  ·
    refine ⟨10970156367100055121497815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14626875156133406828663753 10970156367100055121497815)
    ·
      refine ⟨16455234550650082682246723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10970156367100055121497815 16455234550650082682246723)
      ·
        refine ⟨24682851825975124023370085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16455234550650082682246723 24682851825975124023370085)
        ·
          refine ⟨4628034717370335754381891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24682851825975124023370085 4628034717370335754381891)
          ·
            refine ⟨6942052076055503631572837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4628034717370335754381891 6942052076055503631572837)
            ·
              refine ⟨1301634764260406930919907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6942052076055503631572837 1301634764260406930919907)
              ·
                refine ⟨1952452146390610396379861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1301634764260406930919907 1952452146390610396379861)
                ·
                  refine ⟨45760597181029931165153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1952452146390610396379861 45760597181029931165153)
                  ·
                    rfl

theorem cell22_401033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 7].length) (baseStart_401033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401033 prefixEnd_401033 := by exact prefixLift 401033
  have htrace : WordTrace (prefixWord ++ tailWord_401033) baseStart_401033 baseEnd_401033 := by
    simpa [prefixWord, tailWord_401033, baseEnd_401033] using wordTrace_append hprefix tailTrace_401033
  have hstable : (prefixWord ++ tailWord_401033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401033).length < 2 ^ (prefixWord ++ tailWord_401033).sum := by decide
  have hdescent : baseEnd_401033 < baseStart_401033 := by decide
  rcases family_descends (prefixWord ++ tailWord_401033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401080 : List Nat := [2, 1, 2, 1, 2, 1, 1, 7, 1, 4]
def baseStart_401080 : Nat := 118140960795 + 401080 * 2 ^ 59
def prefixEnd_401080 : Nat := 4983230072969 + 3 ^ 40 * 401080 * 2
def baseEnd_401080 : Nat := 137297880603597337570315

theorem tailTrace_401080 : CollatzResearch.WordTrace tailWord_401080 prefixEnd_401080 137297880603597337570315 := by
  unfold tailWord_401080
  simp only [CollatzResearch.WordTrace]
  refine ⟨7314294693481566927812347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9752392924642089237083129 7314294693481566927812347)
  ·
    refine ⟨10971442040222350391718521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7314294693481566927812347 10971442040222350391718521)
    ·
      refine ⟨8228581530166762793788891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10971442040222350391718521 8228581530166762793788891)
      ·
        refine ⟨12342872295250144190683337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8228581530166762793788891 12342872295250144190683337)
        ·
          refine ⟨9257154221437608143012503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12342872295250144190683337 9257154221437608143012503)
          ·
            refine ⟨13885731332156412214518755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9257154221437608143012503 13885731332156412214518755)
            ·
              refine ⟨20828596998234618321778133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13885731332156412214518755 20828596998234618321778133)
              ·
                refine ⟨488170242146123866916675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20828596998234618321778133 488170242146123866916675)
                ·
                  refine ⟨732255363219185800375013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 488170242146123866916675 732255363219185800375013)
                  ·
                    refine ⟨137297880603597337570315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 732255363219185800375013 137297880603597337570315)
                    ·
                      rfl

theorem cell22_401080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_401080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401080 prefixEnd_401080 := by exact prefixLift 401080
  have htrace : WordTrace (prefixWord ++ tailWord_401080) baseStart_401080 baseEnd_401080 := by
    simpa [prefixWord, tailWord_401080, baseEnd_401080] using wordTrace_append hprefix tailTrace_401080
  have hstable : (prefixWord ++ tailWord_401080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401080).length < 2 ^ (prefixWord ++ tailWord_401080).sum := by decide
  have hdescent : baseEnd_401080 < baseStart_401080 := by decide
  rcases family_descends (prefixWord ++ tailWord_401080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401125 : List Nat := [1, 3, 1, 4, 1, 1, 3, 1, 1, 6]
def baseStart_401125 : Nat := 118140960795 + 401125 * 2 ^ 59
def prefixEnd_401125 : Nat := 4983230072969 + 3 ^ 40 * 401125 * 2
def baseEnd_401125 : Nat := 137313285023232220195177

theorem tailTrace_401125 : CollatzResearch.WordTrace tailWord_401125 prefixEnd_401125 137313285023232220195177 := by
  unfold tailWord_401125
  simp only [CollatzResearch.WordTrace]
  refine ⟨14630230671800106541012829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9753487114533404360675219 14630230671800106541012829)
  ·
    refine ⟨5486336501925039952879811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14630230671800106541012829 5486336501925039952879811)
    ·
      refine ⟨8229504752887559929319717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5486336501925039952879811 8229504752887559929319717)
      ·
        refine ⟨1543032141166417486747447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8229504752887559929319717 1543032141166417486747447)
        ·
          refine ⟨2314548211749626230121171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1543032141166417486747447 2314548211749626230121171)
          ·
            refine ⟨3471822317624439345181757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2314548211749626230121171 3471822317624439345181757)
            ·
              refine ⟨1301933369109164754443159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3471822317624439345181757 1301933369109164754443159)
              ·
                refine ⟨1952900053663747131664739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1301933369109164754443159 1952900053663747131664739)
                ·
                  refine ⟨2929350080495620697497109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1952900053663747131664739 2929350080495620697497109)
                  ·
                    refine ⟨137313285023232220195177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2929350080495620697497109 137313285023232220195177)
                    ·
                      rfl

theorem cell22_401125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_401125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401125 prefixEnd_401125 := by exact prefixLift 401125
  have htrace : WordTrace (prefixWord ++ tailWord_401125) baseStart_401125 baseEnd_401125 := by
    simpa [prefixWord, tailWord_401125, baseEnd_401125] using wordTrace_append hprefix tailTrace_401125
  have hstable : (prefixWord ++ tailWord_401125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401125).length < 2 ^ (prefixWord ++ tailWord_401125).sum := by decide
  have hdescent : baseEnd_401125 < baseStart_401125 := by decide
  rcases family_descends (prefixWord ++ tailWord_401125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401165 : List Nat := [1, 7, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_401165 : Nat := 118140960795 + 401165 * 2 ^ 59
def prefixEnd_401165 : Nat := 4983230072969 + 3 ^ 40 * 401165 * 2
def baseEnd_401165 : Nat := 137326977840685449195055

theorem tailTrace_401165 : CollatzResearch.WordTrace tailWord_401165 prefixEnd_401165 137326977840685449195055 := by
  unfold tailWord_401165
  simp only [CollatzResearch.WordTrace]
  refine ⟨14631689591655193372468949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9754459727770128914979299 14631689591655193372468949)
  ·
    refine ⟨342930224804418594667241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 14631689591655193372468949 342930224804418594667241)
    ·
      refine ⟨257197668603313946000431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342930224804418594667241 257197668603313946000431)
      ·
        refine ⟨385796502904970919000647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257197668603313946000431 385796502904970919000647)
        ·
          refine ⟨578694754357456378500971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385796502904970919000647 578694754357456378500971)
          ·
            refine ⟨868042131536184567751457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578694754357456378500971 868042131536184567751457)
            ·
              refine ⟨651031598652138425813593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 868042131536184567751457 651031598652138425813593)
              ·
                refine ⟨488273698989103819360195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 651031598652138425813593 488273698989103819360195)
                ·
                  refine ⟨732410548483655729040293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 488273698989103819360195 732410548483655729040293)
                  ·
                    refine ⟨137326977840685449195055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 732410548483655729040293 137326977840685449195055)
                    ·
                      rfl

theorem cell22_401165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_401165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401165 prefixEnd_401165 := by exact prefixLift 401165
  have htrace : WordTrace (prefixWord ++ tailWord_401165) baseStart_401165 baseEnd_401165 := by
    simpa [prefixWord, tailWord_401165, baseEnd_401165] using wordTrace_append hprefix tailTrace_401165
  have hstable : (prefixWord ++ tailWord_401165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401165).length < 2 ^ (prefixWord ++ tailWord_401165).sum := by decide
  have hdescent : baseEnd_401165 < baseStart_401165 := by decide
  rcases family_descends (prefixWord ++ tailWord_401165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401185 : List Nat := [1, 2, 3, 2, 1, 3, 1, 2, 7]
def baseStart_401185 : Nat := 118140960795 + 401185 * 2 ^ 59
def prefixEnd_401185 : Nat := 4983230072969 + 3 ^ 40 * 401185 * 2
def baseEnd_401185 : Nat := 45777941416470687898331

theorem tailTrace_401185 : CollatzResearch.WordTrace tailWord_401185 prefixEnd_401185 45777941416470687898331 := by
  unfold tailWord_401185
  simp only [CollatzResearch.WordTrace]
  refine ⟨14632419051582736788197009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9754946034388491192131339 14632419051582736788197009)
  ·
    refine ⟨10974314288687052591147757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14632419051582736788197009 10974314288687052591147757)
    ·
      refine ⟨4115367858257644721680409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10974314288687052591147757 4115367858257644721680409)
      ·
        refine ⟨3086525893693233541260307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4115367858257644721680409 3086525893693233541260307)
        ·
          refine ⟨4629788840539850311890461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3086525893693233541260307 4629788840539850311890461)
          ·
            refine ⟨1736170815202443866958923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4629788840539850311890461 1736170815202443866958923)
            ·
              refine ⟨2604256222803665800438385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1736170815202443866958923 2604256222803665800438385)
              ·
                refine ⟨1953192167102749350328789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2604256222803665800438385 1953192167102749350328789)
                ·
                  refine ⟨45777941416470687898331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1953192167102749350328789 45777941416470687898331)
                  ·
                    rfl

theorem cell22_401185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 7].length) (baseStart_401185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401185 prefixEnd_401185 := by exact prefixLift 401185
  have htrace : WordTrace (prefixWord ++ tailWord_401185) baseStart_401185 baseEnd_401185 := by
    simpa [prefixWord, tailWord_401185, baseEnd_401185] using wordTrace_append hprefix tailTrace_401185
  have hstable : (prefixWord ++ tailWord_401185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401185).length < 2 ^ (prefixWord ++ tailWord_401185).sum := by decide
  have hdescent : baseEnd_401185 < baseStart_401185 := by decide
  rcases family_descends (prefixWord ++ tailWord_401185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401206 : List Nat := [5, 1, 2, 2, 1, 1, 3, 1, 3, 3]
def baseStart_401206 : Nat := 118140960795 + 401206 * 2 ^ 59
def prefixEnd_401206 : Nat := 4983230072969 + 3 ^ 40 * 401206 * 2
def baseEnd_401206 : Nat := 137341012978575008919929

theorem tailTrace_401206 : CollatzResearch.WordTrace tailWord_401206 prefixEnd_401206 137341012978575008919929 := by
  unfold tailWord_401206
  simp only [CollatzResearch.WordTrace]
  refine ⟨914574061531666085919467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9755456656337771583140981 914574061531666085919467)
  ·
    refine ⟨1371861092297499128879201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 914574061531666085919467 1371861092297499128879201)
    ·
      refine ⟨1028895819223124346659401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1371861092297499128879201 1028895819223124346659401)
      ·
        refine ⟨771671864417343259994551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1028895819223124346659401 771671864417343259994551)
        ·
          refine ⟨1157507796626014889991827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 771671864417343259994551 1157507796626014889991827)
          ·
            refine ⟨1736261694939022334987741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1157507796626014889991827 1736261694939022334987741)
            ·
              refine ⟨651098135602133375620403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1736261694939022334987741 651098135602133375620403)
              ·
                refine ⟨976647203403200063430605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 651098135602133375620403 976647203403200063430605)
                ·
                  refine ⟨366242701276200023786477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 976647203403200063430605 366242701276200023786477)
                  ·
                    refine ⟨137341012978575008919929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 366242701276200023786477 137341012978575008919929)
                    ·
                      rfl

theorem cell22_401206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_401206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401206 prefixEnd_401206 := by exact prefixLift 401206
  have htrace : WordTrace (prefixWord ++ tailWord_401206) baseStart_401206 baseEnd_401206 := by
    simpa [prefixWord, tailWord_401206, baseEnd_401206] using wordTrace_append hprefix tailTrace_401206
  have hstable : (prefixWord ++ tailWord_401206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401206).length < 2 ^ (prefixWord ++ tailWord_401206).sum := by decide
  have hdescent : baseEnd_401206 < baseStart_401206 := by decide
  rcases family_descends (prefixWord ++ tailWord_401206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401219 : List Nat := [1, 1, 1, 3, 1, 7, 2, 1, 5]
def baseStart_401219 : Nat := 118140960795 + 401219 * 2 ^ 59
def prefixEnd_401219 : Nat := 4983230072969 + 3 ^ 40 * 401219 * 2
def baseEnd_401219 : Nat := 45781821048082436114963

theorem tailTrace_401219 : CollatzResearch.WordTrace tailWord_401219 prefixEnd_401219 45781821048082436114963 := by
  unfold tailWord_401219
  simp only [CollatzResearch.WordTrace]
  refine ⟨14633659133459560594934711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9755772755639707063289807 14633659133459560594934711)
  ·
    refine ⟨21950488700189340892402067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14633659133459560594934711 21950488700189340892402067)
    ·
      refine ⟨32925733050284011338603101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21950488700189340892402067 32925733050284011338603101)
      ·
        refine ⟨12347149893856504251976163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32925733050284011338603101 12347149893856504251976163)
        ·
          refine ⟨18520724840784756377964245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12347149893856504251976163 18520724840784756377964245)
          ·
            refine ⟨434079488455892727608537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 18520724840784756377964245 434079488455892727608537)
            ·
              refine ⟨325559616341919545706403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 434079488455892727608537 325559616341919545706403)
              ·
                refine ⟨488339424512879318559605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325559616341919545706403 488339424512879318559605)
                ·
                  refine ⟨45781821048082436114963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 488339424512879318559605 45781821048082436114963)
                  ·
                    rfl

theorem cell22_401219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 5].length) (baseStart_401219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401219 prefixEnd_401219 := by exact prefixLift 401219
  have htrace : WordTrace (prefixWord ++ tailWord_401219) baseStart_401219 baseEnd_401219 := by
    simpa [prefixWord, tailWord_401219, baseEnd_401219] using wordTrace_append hprefix tailTrace_401219
  have hstable : (prefixWord ++ tailWord_401219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401219).length < 2 ^ (prefixWord ++ tailWord_401219).sum := by decide
  have hdescent : baseEnd_401219 < baseStart_401219 := by decide
  rcases family_descends (prefixWord ++ tailWord_401219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401249 : List Nat := [1, 2, 3, 1, 1, 1, 7, 1, 1, 4]
def baseStart_401249 : Nat := 118140960795 + 401249 * 2 ^ 59
def prefixEnd_401249 : Nat := 4983230072969 + 3 ^ 40 * 401249 * 2
def baseEnd_401249 : Nat := 137355732757337230094797

theorem tailTrace_401249 : CollatzResearch.WordTrace tailWord_401249 prefixEnd_401249 137355732757337230094797 := by
  unfold tailWord_401249
  simp only [CollatzResearch.WordTrace]
  refine ⟨14634753323350875718526801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9756502215567250479017867 14634753323350875718526801)
  ·
    refine ⟨10976064992513156788895101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14634753323350875718526801 10976064992513156788895101)
    ·
      refine ⟨4116024372192433795835663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10976064992513156788895101 4116024372192433795835663)
      ·
        refine ⟨6174036558288650693753495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4116024372192433795835663 6174036558288650693753495)
        ·
          refine ⟨9261054837432976040630243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6174036558288650693753495 9261054837432976040630243)
          ·
            refine ⟨13891582256149464060945365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9261054837432976040630243 13891582256149464060945365)
            ·
              refine ⟨325583959128503063928407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 13891582256149464060945365 325583959128503063928407)
              ·
                refine ⟨488375938692754595892611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325583959128503063928407 488375938692754595892611)
                ·
                  refine ⟨732563908039131893838917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 488375938692754595892611 732563908039131893838917)
                  ·
                    refine ⟨137355732757337230094797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 732563908039131893838917 137355732757337230094797)
                    ·
                      rfl

theorem cell22_401249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_401249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401249 prefixEnd_401249 := by exact prefixLift 401249
  have htrace : WordTrace (prefixWord ++ tailWord_401249) baseStart_401249 baseEnd_401249 := by
    simpa [prefixWord, tailWord_401249, baseEnd_401249] using wordTrace_append hprefix tailTrace_401249
  have hstable : (prefixWord ++ tailWord_401249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401249).length < 2 ^ (prefixWord ++ tailWord_401249).sum := by decide
  have hdescent : baseEnd_401249 < baseStart_401249 := by decide
  rcases family_descends (prefixWord ++ tailWord_401249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401313 : List Nat := [1, 2, 3, 4, 2, 2, 1, 2, 2, 3]
def baseStart_401313 : Nat := 118140960795 + 401313 * 2 ^ 59
def prefixEnd_401313 : Nat := 4983230072969 + 3 ^ 40 * 401313 * 2
def baseEnd_401313 : Nat := 137377641265262396494601

theorem tailTrace_401313 : CollatzResearch.WordTrace tailWord_401313 prefixEnd_401313 137377641265262396494601 := by
  unfold tailWord_401313
  simp only [CollatzResearch.WordTrace]
  refine ⟨14637087595119014648856593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9758058396746009765904395 14637087595119014648856593)
  ·
    refine ⟨10977815696339260986642445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14637087595119014648856593 10977815696339260986642445)
    ·
      refine ⟨4116680886127222869990917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10977815696339260986642445 4116680886127222869990917)
      ·
        refine ⟨771877666148854288123297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4116680886127222869990917 771877666148854288123297)
        ·
          refine ⟨578908249611640716092473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 771877666148854288123297 578908249611640716092473)
          ·
            refine ⟨434181187208730537069355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 578908249611640716092473 434181187208730537069355)
            ·
              refine ⟨651271780813095805604033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434181187208730537069355 651271780813095805604033)
              ·
                refine ⟨488453835609821854203025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 651271780813095805604033 488453835609821854203025)
                ·
                  refine ⟨366340376707366390652269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 488453835609821854203025 366340376707366390652269)
                  ·
                    refine ⟨137377641265262396494601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 366340376707366390652269 137377641265262396494601)
                    ·
                      rfl

theorem cell22_401313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_401313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401313 prefixEnd_401313 := by exact prefixLift 401313
  have htrace : WordTrace (prefixWord ++ tailWord_401313) baseStart_401313 baseEnd_401313 := by
    simpa [prefixWord, tailWord_401313, baseEnd_401313] using wordTrace_append hprefix tailTrace_401313
  have hstable : (prefixWord ++ tailWord_401313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401313).length < 2 ^ (prefixWord ++ tailWord_401313).sum := by decide
  have hdescent : baseEnd_401313 < baseStart_401313 := by decide
  rcases family_descends (prefixWord ++ tailWord_401313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401401 : List Nat := [1, 2, 1, 3, 1, 6, 1, 2, 1, 4]
def baseStart_401401 : Nat := 118140960795 + 401401 * 2 ^ 59
def prefixEnd_401401 : Nat := 4983230072969 + 3 ^ 40 * 401401 * 2
def baseEnd_401401 : Nat := 137407765463659500294331

theorem tailTrace_401401 : CollatzResearch.WordTrace tailWord_401401 prefixEnd_401401 137407765463659500294331 := by
  unfold tailWord_401401
  simp only [CollatzResearch.WordTrace]
  refine ⟨14640297218800205678060057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9760198145866803785373371 14640297218800205678060057)
  ·
    refine ⟨10980222914100154258545043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14640297218800205678060057 10980222914100154258545043)
    ·
      refine ⟨16470334371150231387817565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10980222914100154258545043 16470334371150231387817565)
      ·
        refine ⟨6176375389181336770431587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16470334371150231387817565 6176375389181336770431587)
        ·
          refine ⟨9264563083772005155647381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6176375389181336770431587 9264563083772005155647381)
          ·
            refine ⟨434276394551812741670971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9264563083772005155647381 434276394551812741670971)
            ·
              refine ⟨651414591827719112506457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434276394551812741670971 651414591827719112506457)
              ·
                refine ⟨488560943870789334379843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 651414591827719112506457 488560943870789334379843)
                ·
                  refine ⟨732841415806184001569765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 488560943870789334379843 732841415806184001569765)
                  ·
                    refine ⟨137407765463659500294331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 732841415806184001569765 137407765463659500294331)
                    ·
                      rfl

theorem cell22_401401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 4].length) (baseStart_401401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401401 prefixEnd_401401 := by exact prefixLift 401401
  have htrace : WordTrace (prefixWord ++ tailWord_401401) baseStart_401401 baseEnd_401401 := by
    simpa [prefixWord, tailWord_401401, baseEnd_401401] using wordTrace_append hprefix tailTrace_401401
  have hstable : (prefixWord ++ tailWord_401401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401401).length < 2 ^ (prefixWord ++ tailWord_401401).sum := by decide
  have hdescent : baseEnd_401401 < baseStart_401401 := by decide
  rcases family_descends (prefixWord ++ tailWord_401401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401418 : List Nat := [3, 1, 2, 2, 4, 1, 3, 1, 1, 4]
def baseStart_401418 : Nat := 118140960795 + 401418 * 2 ^ 59
def prefixEnd_401418 : Nat := 4983230072969 + 3 ^ 40 * 401418 * 2
def baseEnd_401418 : Nat := 137413584911077122619279

theorem tailTrace_401418 : CollatzResearch.WordTrace tailWord_401418 prefixEnd_401418 137413584911077122619279 := by
  unfold tailWord_401418
  simp only [CollatzResearch.WordTrace]
  refine ⟨3660229314934654395357227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9760611506492411720952605 3660229314934654395357227)
  ·
    refine ⟨5490343972401981593035841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3660229314934654395357227 5490343972401981593035841)
    ·
      refine ⟨4117757979301486194776881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5490343972401981593035841 4117757979301486194776881)
      ·
        refine ⟨3088318484476114646082661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4117757979301486194776881 3088318484476114646082661)
        ·
          refine ⟨579059715839271496140499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3088318484476114646082661 579059715839271496140499)
          ·
            refine ⟨868589573758907244210749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579059715839271496140499 868589573758907244210749)
            ·
              refine ⟨325721090159590216579031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 868589573758907244210749 325721090159590216579031)
              ·
                refine ⟨488581635239385324868547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325721090159590216579031 488581635239385324868547)
                ·
                  refine ⟨732872452859077987302821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 488581635239385324868547 732872452859077987302821)
                  ·
                    refine ⟨137413584911077122619279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 732872452859077987302821 137413584911077122619279)
                    ·
                      rfl

theorem cell22_401418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_401418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401418 prefixEnd_401418 := by exact prefixLift 401418
  have htrace : WordTrace (prefixWord ++ tailWord_401418) baseStart_401418 baseEnd_401418 := by
    simpa [prefixWord, tailWord_401418, baseEnd_401418] using wordTrace_append hprefix tailTrace_401418
  have hstable : (prefixWord ++ tailWord_401418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401418).length < 2 ^ (prefixWord ++ tailWord_401418).sum := by decide
  have hdescent : baseEnd_401418 < baseStart_401418 := by decide
  rcases family_descends (prefixWord ++ tailWord_401418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401448 : List Nat := [2, 1, 5, 3, 1, 1, 2, 1, 1, 5]
def baseStart_401448 : Nat := 118140960795 + 401448 * 2 ^ 59
def prefixEnd_401448 : Nat := 4983230072969 + 3 ^ 40 * 401448 * 2
def baseEnd_401448 : Nat := 137423854524167044369187

theorem tailTrace_401448 : CollatzResearch.WordTrace tailWord_401448 prefixEnd_401448 137423854524167044369187 := by
  unfold tailWord_401448
  simp only [CollatzResearch.WordTrace]
  refine ⟨7321005724814966352510499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9761340966419955136680665 7321005724814966352510499)
  ·
    refine ⟨10981508587222449528765749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7321005724814966352510499 10981508587222449528765749)
    ·
      refine ⟨1029516430052104643321789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10981508587222449528765749 1029516430052104643321789)
      ·
        refine ⟨386068661269539241245671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1029516430052104643321789 386068661269539241245671)
        ·
          refine ⟨579102991904308861868507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386068661269539241245671 579102991904308861868507)
          ·
            refine ⟨868654487856463292802761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579102991904308861868507 868654487856463292802761)
            ·
              refine ⟨651490865892347469602071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 868654487856463292802761 651490865892347469602071)
              ·
                refine ⟨977236298838521204403107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 651490865892347469602071 977236298838521204403107)
                ·
                  refine ⟨1465854448257781806604661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 977236298838521204403107 1465854448257781806604661)
                  ·
                    refine ⟨137423854524167044369187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1465854448257781806604661 137423854524167044369187)
                    ·
                      rfl

theorem cell22_401448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_401448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401448 prefixEnd_401448 := by exact prefixLift 401448
  have htrace : WordTrace (prefixWord ++ tailWord_401448) baseStart_401448 baseEnd_401448 := by
    simpa [prefixWord, tailWord_401448, baseEnd_401448] using wordTrace_append hprefix tailTrace_401448
  have hstable : (prefixWord ++ tailWord_401448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401448).length < 2 ^ (prefixWord ++ tailWord_401448).sum := by decide
  have hdescent : baseEnd_401448 < baseStart_401448 := by decide
  rcases family_descends (prefixWord ++ tailWord_401448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401459 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 5, 3]
def baseStart_401459 : Nat := 118140960795 + 401459 * 2 ^ 59
def prefixEnd_401459 : Nat := 4983230072969 + 3 ^ 40 * 401459 * 2
def baseEnd_401459 : Nat := 137427620048966682344153

theorem tailTrace_401459 : CollatzResearch.WordTrace tailWord_401459 prefixEnd_401459 137427620048966682344153 := by
  unfold tailWord_401459
  simp only [CollatzResearch.WordTrace]
  refine ⟨14642412652590081583671431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9761608435060054389114287 14642412652590081583671431)
  ·
    refine ⟨21963618978885122375507147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14642412652590081583671431 21963618978885122375507147)
    ·
      refine ⟨32945428468327683563260721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21963618978885122375507147 32945428468327683563260721)
      ·
        refine ⟨24709071351245762672445541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32945428468327683563260721 24709071351245762672445541)
        ·
          refine ⟨4632950878358580501083539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24709071351245762672445541 4632950878358580501083539)
          ·
            refine ⟨6949426317537870751625309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4632950878358580501083539 6949426317537870751625309)
            ·
              refine ⟨2606034869076701531859491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6949426317537870751625309 2606034869076701531859491)
              ·
                refine ⟨3909052303615052297789237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2606034869076701531859491 3909052303615052297789237)
                ·
                  refine ⟨366473653463911152917741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3909052303615052297789237 366473653463911152917741)
                  ·
                    refine ⟨137427620048966682344153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 366473653463911152917741 137427620048966682344153)
                    ·
                      rfl

theorem cell22_401459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5, 3].length) (baseStart_401459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401459 prefixEnd_401459 := by exact prefixLift 401459
  have htrace : WordTrace (prefixWord ++ tailWord_401459) baseStart_401459 baseEnd_401459 := by
    simpa [prefixWord, tailWord_401459, baseEnd_401459] using wordTrace_append hprefix tailTrace_401459
  have hstable : (prefixWord ++ tailWord_401459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401459).length < 2 ^ (prefixWord ++ tailWord_401459).sum := by decide
  have hdescent : baseEnd_401459 < baseStart_401459 := by decide
  rcases family_descends (prefixWord ++ tailWord_401459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401487 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 3, 7]
def baseStart_401487 : Nat := 118140960795 + 401487 * 2 ^ 59
def prefixEnd_401487 : Nat := 4983230072969 + 3 ^ 40 * 401487 * 2
def baseEnd_401487 : Nat := 137437205021183942644067

theorem tailTrace_401487 : CollatzResearch.WordTrace tailWord_401487 prefixEnd_401487 137437205021183942644067 := by
  unfold tailWord_401487
  simp only [CollatzResearch.WordTrace]
  refine ⟨14643433896488642365690715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9762289264325761577127143 14643433896488642365690715)
  ·
    refine ⟨21965150844732963548536073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14643433896488642365690715 21965150844732963548536073)
    ·
      refine ⟨16473863133549722661402055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21965150844732963548536073 16473863133549722661402055)
      ·
        refine ⟨24710794700324583992103083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16473863133549722661402055 24710794700324583992103083)
        ·
          refine ⟨37066192050486875988154625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24710794700324583992103083 37066192050486875988154625)
          ·
            refine ⟨27799644037865156991115969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37066192050486875988154625 27799644037865156991115969)
            ·
              refine ⟨20849733028398867743336977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27799644037865156991115969 20849733028398867743336977)
              ·
                refine ⟨15637299771299150807502733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20849733028398867743336977 15637299771299150807502733)
                ·
                  refine ⟨5863987414237181552813525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15637299771299150807502733 5863987414237181552813525)
                  ·
                    refine ⟨137437205021183942644067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5863987414237181552813525 137437205021183942644067)
                    ·
                      rfl

theorem cell22_401487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 7].length) (baseStart_401487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401487 prefixEnd_401487 := by exact prefixLift 401487
  have htrace : WordTrace (prefixWord ++ tailWord_401487) baseStart_401487 baseEnd_401487 := by
    simpa [prefixWord, tailWord_401487, baseEnd_401487] using wordTrace_append hprefix tailTrace_401487
  have hstable : (prefixWord ++ tailWord_401487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401487).length < 2 ^ (prefixWord ++ tailWord_401487).sum := by decide
  have hdescent : baseEnd_401487 < baseStart_401487 := by decide
  rcases family_descends (prefixWord ++ tailWord_401487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401493 : List Nat := [1, 3, 2, 2, 1, 3, 2, 4, 1, 3]
def baseStart_401493 : Nat := 118140960795 + 401493 * 2 ^ 59
def prefixEnd_401493 : Nat := 4983230072969 + 3 ^ 40 * 401493 * 2
def baseEnd_401493 : Nat := 137439258943801926994049

theorem tailTrace_401493 : CollatzResearch.WordTrace tailWord_401493 prefixEnd_401493 137439258943801926994049 := by
  unfold tailWord_401493
  simp only [CollatzResearch.WordTrace]
  refine ⟨14643652734466905390409133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9762435156311270260272755 14643652734466905390409133)
  ·
    refine ⟨5491369775425089521403425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14643652734466905390409133 5491369775425089521403425)
    ·
      refine ⟨4118527331568817141052569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5491369775425089521403425 4118527331568817141052569)
      ·
        refine ⟨3088895498676612855789427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4118527331568817141052569 3088895498676612855789427)
        ·
          refine ⟨4633343248014919283684141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3088895498676612855789427 4633343248014919283684141)
          ·
            refine ⟨1737503718005594731381553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4633343248014919283684141 1737503718005594731381553)
            ·
              refine ⟨1303127788504196048536165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1737503718005594731381553 1303127788504196048536165)
              ·
                refine ⟨244336460344536759100531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1303127788504196048536165 244336460344536759100531)
                ·
                  refine ⟨366504690516805138650797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244336460344536759100531 366504690516805138650797)
                  ·
                    refine ⟨137439258943801926994049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 366504690516805138650797 137439258943801926994049)
                    ·
                      rfl

theorem cell22_401493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_401493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401493 prefixEnd_401493 := by exact prefixLift 401493
  have htrace : WordTrace (prefixWord ++ tailWord_401493) baseStart_401493 baseEnd_401493 := by
    simpa [prefixWord, tailWord_401493, baseEnd_401493] using wordTrace_append hprefix tailTrace_401493
  have hstable : (prefixWord ++ tailWord_401493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401493).length < 2 ^ (prefixWord ++ tailWord_401493).sum := by decide
  have hdescent : baseEnd_401493 < baseStart_401493 := by decide
  rcases family_descends (prefixWord ++ tailWord_401493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401504 : List Nat := [2, 1, 1, 3, 2, 3, 2, 1, 2, 5]
def baseStart_401504 : Nat := 118140960795 + 401504 * 2 ^ 59
def prefixEnd_401504 : Nat := 4983230072969 + 3 ^ 40 * 401504 * 2
def baseEnd_401504 : Nat := 137443024468601564969015

theorem tailTrace_401504 : CollatzResearch.WordTrace tailWord_401504 prefixEnd_401504 137443024468601564969015 := by
  unfold tailWord_401504
  simp only [CollatzResearch.WordTrace]
  refine ⟨7322026968713527134529783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9762702624951369512706377 7322026968713527134529783)
  ·
    refine ⟨10983040453070290701794675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7322026968713527134529783 10983040453070290701794675)
    ·
      refine ⟨16474560679605436052692013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10983040453070290701794675 16474560679605436052692013)
      ·
        refine ⟨6177960254852038519759505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16474560679605436052692013 6177960254852038519759505)
        ·
          refine ⟨4633470191139028889819629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6177960254852038519759505 4633470191139028889819629)
          ·
            refine ⟨1737551321677135833682361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4633470191139028889819629 1737551321677135833682361)
            ·
              refine ⟨1303163491257851875261771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1737551321677135833682361 1303163491257851875261771)
              ·
                refine ⟨1954745236886777812892657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1303163491257851875261771 1954745236886777812892657)
                ·
                  refine ⟨1466058927665083359669493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1954745236886777812892657 1466058927665083359669493)
                  ·
                    refine ⟨137443024468601564969015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1466058927665083359669493 137443024468601564969015)
                    ·
                      rfl

theorem cell22_401504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 2, 5].length) (baseStart_401504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401504 prefixEnd_401504 := by exact prefixLift 401504
  have htrace : WordTrace (prefixWord ++ tailWord_401504) baseStart_401504 baseEnd_401504 := by
    simpa [prefixWord, tailWord_401504, baseEnd_401504] using wordTrace_append hprefix tailTrace_401504
  have hstable : (prefixWord ++ tailWord_401504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401504).length < 2 ^ (prefixWord ++ tailWord_401504).sum := by decide
  have hdescent : baseEnd_401504 < baseStart_401504 := by decide
  rcases family_descends (prefixWord ++ tailWord_401504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401570 : List Nat := [3, 3, 1, 3, 1, 3, 1, 2, 1, 4]
def baseStart_401570 : Nat := 118140960795 + 401570 * 2 ^ 59
def prefixEnd_401570 : Nat := 4983230072969 + 3 ^ 40 * 401570 * 2
def baseEnd_401570 : Nat := 137465617617399392818813

theorem tailTrace_401570 : CollatzResearch.WordTrace tailWord_401570 prefixEnd_401570 137465617617399392818813 := by
  unfold tailWord_401570
  simp only [CollatzResearch.WordTrace]
  refine ⟨3661615288796986885240541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9764307436791965027308109 3661615288796986885240541)
  ·
    refine ⟨1373105733298870081965203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3661615288796986885240541 1373105733298870081965203)
    ·
      refine ⟨2059658599948305122947805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1373105733298870081965203 2059658599948305122947805)
      ·
        refine ⟨772371974980614421105427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2059658599948305122947805 772371974980614421105427)
        ·
          refine ⟨1158557962470921631658141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 772371974980614421105427 1158557962470921631658141)
          ·
            refine ⟨434459235926595611871803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1158557962470921631658141 434459235926595611871803)
            ·
              refine ⟨651688853889893417807705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434459235926595611871803 651688853889893417807705)
              ·
                refine ⟨488766640417420063355779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 651688853889893417807705 488766640417420063355779)
                ·
                  refine ⟨733149960626130095033669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 488766640417420063355779 733149960626130095033669)
                  ·
                    refine ⟨137465617617399392818813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 733149960626130095033669 137465617617399392818813)
                    ·
                      rfl

theorem cell22_401570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_401570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401570 prefixEnd_401570 := by exact prefixLift 401570
  have htrace : WordTrace (prefixWord ++ tailWord_401570) baseStart_401570 baseEnd_401570 := by
    simpa [prefixWord, tailWord_401570, baseEnd_401570] using wordTrace_append hprefix tailTrace_401570
  have hstable : (prefixWord ++ tailWord_401570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401570).length < 2 ^ (prefixWord ++ tailWord_401570).sum := by decide
  have hdescent : baseEnd_401570 < baseStart_401570 := by decide
  rcases family_descends (prefixWord ++ tailWord_401570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401596 : List Nat := [2, 2, 2, 3, 4, 9]
def baseStart_401596 : Nat := 118140960795 + 401596 * 2 ^ 59
def prefixEnd_401596 : Nat := 4983230072969 + 3 ^ 40 * 401596 * 2
def baseEnd_401596 : Nat := 1697216270972148045293

theorem tailTrace_401596 : CollatzResearch.WordTrace tailWord_401596 prefixEnd_401596 1697216270972148045293 := by
  unfold tailWord_401596
  simp only [CollatzResearch.WordTrace]
  refine ⟨7323704726546876990704321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9764939635395835987605761 7323704726546876990704321)
  ·
    refine ⟨5492778544910157743028241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7323704726546876990704321 5492778544910157743028241)
    ·
      refine ⟨4119583908682618307271181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5492778544910157743028241 4119583908682618307271181)
      ·
        refine ⟨1544843965755981865226693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4119583908682618307271181 1544843965755981865226693)
        ·
          refine ⟨289658243579246599730005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1544843965755981865226693 289658243579246599730005)
          ·
            refine ⟨1697216270972148045293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 289658243579246599730005 1697216270972148045293)
            ·
              rfl

theorem cell22_401596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 9].length) (baseStart_401596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401596 prefixEnd_401596 := by exact prefixLift 401596
  have htrace : WordTrace (prefixWord ++ tailWord_401596) baseStart_401596 baseEnd_401596 := by
    simpa [prefixWord, tailWord_401596, baseEnd_401596] using wordTrace_append hprefix tailTrace_401596
  have hstable : (prefixWord ++ tailWord_401596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401596).length < 2 ^ (prefixWord ++ tailWord_401596).sum := by decide
  have hdescent : baseEnd_401596 < baseStart_401596 := by decide
  rcases family_descends (prefixWord ++ tailWord_401596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401602 : List Nat := [3, 5, 1, 1, 1, 2, 1, 4, 4]
def baseStart_401602 : Nat := 118140960795 + 401602 * 2 ^ 59
def prefixEnd_401602 : Nat := 4983230072969 + 3 ^ 40 * 401602 * 2
def baseEnd_401602 : Nat := 45825523957120658672905

theorem tailTrace_401602 : CollatzResearch.WordTrace tailWord_401602 prefixEnd_401602 45825523957120658672905 := by
  unfold tailWord_401602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3661907072768004251531765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9765085527381344670751373 3661907072768004251531765)
  ·
    refine ⟨343303788072000398581103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3661907072768004251531765 343303788072000398581103)
    ·
      refine ⟨514955682108000597871655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343303788072000398581103 514955682108000597871655)
      ·
        refine ⟨772433523162000896807483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514955682108000597871655 772433523162000896807483)
        ·
          refine ⟨1158650284743001345211225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 772433523162000896807483 1158650284743001345211225)
          ·
            refine ⟨868987713557251008908419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1158650284743001345211225 868987713557251008908419)
            ·
              refine ⟨1303481570335876513362629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 868987713557251008908419 1303481570335876513362629)
              ·
                refine ⟨244402794437976846255493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1303481570335876513362629 244402794437976846255493)
                ·
                  refine ⟨45825523957120658672905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 244402794437976846255493 45825523957120658672905)
                  ·
                    rfl

theorem cell22_401602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_401602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401602 prefixEnd_401602 := by exact prefixLift 401602
  have htrace : WordTrace (prefixWord ++ tailWord_401602) baseStart_401602 baseEnd_401602 := by
    simpa [prefixWord, tailWord_401602, baseEnd_401602] using wordTrace_append hprefix tailTrace_401602
  have hstable : (prefixWord ++ tailWord_401602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401602).length < 2 ^ (prefixWord ++ tailWord_401602).sum := by decide
  have hdescent : baseEnd_401602 < baseStart_401602 := by decide
  rcases family_descends (prefixWord ++ tailWord_401602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401611 : List Nat := [1, 1, 1, 1, 3, 2, 4, 3, 3, 3]
def baseStart_401611 : Nat := 118140960795 + 401611 * 2 ^ 59
def prefixEnd_401611 : Nat := 4983230072969 + 3 ^ 40 * 401611 * 2
def baseEnd_401611 : Nat := 137479652755288952543687

theorem tailTrace_401611 : CollatzResearch.WordTrace tailWord_401611 prefixEnd_401611 137479652755288952543687 := by
  unfold tailWord_401611
  simp only [CollatzResearch.WordTrace]
  refine ⟨14647956548039411543204687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9765304365359607695469791 14647956548039411543204687)
  ·
    refine ⟨21971934822059117314807031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14647956548039411543204687 21971934822059117314807031)
    ·
      refine ⟨32957902233088675972210547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21971934822059117314807031 32957902233088675972210547)
      ·
        refine ⟨49436853349633013958315821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32957902233088675972210547 49436853349633013958315821)
        ·
          refine ⟨18538820006112380234368433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49436853349633013958315821 18538820006112380234368433)
          ·
            refine ⟨13904115004584285175776325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18538820006112380234368433 13904115004584285175776325)
            ·
              refine ⟨2607021563359553470458061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13904115004584285175776325 2607021563359553470458061)
              ·
                refine ⟨977633086259832551421773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2607021563359553470458061 977633086259832551421773)
                ·
                  refine ⟨366612407347437206783165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 977633086259832551421773 366612407347437206783165)
                  ·
                    refine ⟨137479652755288952543687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 366612407347437206783165 137479652755288952543687)
                    ·
                      rfl

theorem cell22_401611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3, 3].length) (baseStart_401611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401611 prefixEnd_401611 := by exact prefixLift 401611
  have htrace : WordTrace (prefixWord ++ tailWord_401611) baseStart_401611 baseEnd_401611 := by
    simpa [prefixWord, tailWord_401611, baseEnd_401611] using wordTrace_append hprefix tailTrace_401611
  have hstable : (prefixWord ++ tailWord_401611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401611).length < 2 ^ (prefixWord ++ tailWord_401611).sum := by decide
  have hdescent : baseEnd_401611 < baseStart_401611 := by decide
  rcases family_descends (prefixWord ++ tailWord_401611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401658 : List Nat := [3, 1, 1, 1, 1, 7, 1, 2, 5]
def baseStart_401658 : Nat := 118140960795 + 401658 * 2 ^ 59
def prefixEnd_401658 : Nat := 4983230072969 + 3 ^ 40 * 401658 * 2
def baseEnd_401658 : Nat := 45831913938598832206181

theorem tailTrace_401658 : CollatzResearch.WordTrace tailWord_401658 prefixEnd_401658 45831913938598832206181 := by
  unfold tailWord_401658
  simp only [CollatzResearch.WordTrace]
  refine ⟨3662417694717284642541407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9766447185912759046777085 3662417694717284642541407)
  ·
    refine ⟨5493626542075926963812111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3662417694717284642541407 5493626542075926963812111)
    ·
      refine ⟨8240439813113890445718167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5493626542075926963812111 8240439813113890445718167)
      ·
        refine ⟨12360659719670835668577251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8240439813113890445718167 12360659719670835668577251)
        ·
          refine ⟨18540989579506253502865877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12360659719670835668577251 18540989579506253502865877)
          ·
            refine ⟨434554443269677816473419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 18540989579506253502865877 434554443269677816473419)
            ·
              refine ⟨651831664904516724710129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434554443269677816473419 651831664904516724710129)
              ·
                refine ⟨488873748678387543532597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 651831664904516724710129 488873748678387543532597)
                ·
                  refine ⟨45831913938598832206181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 488873748678387543532597 45831913938598832206181)
                  ·
                    rfl

theorem cell22_401658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 5].length) (baseStart_401658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401658 prefixEnd_401658 := by exact prefixLift 401658
  have htrace : WordTrace (prefixWord ++ tailWord_401658) baseStart_401658 baseEnd_401658 := by
    simpa [prefixWord, tailWord_401658, baseEnd_401658] using wordTrace_append hprefix tailTrace_401658
  have hstable : (prefixWord ++ tailWord_401658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401658).length < 2 ^ (prefixWord ++ tailWord_401658).sum := by decide
  have hdescent : baseEnd_401658 < baseStart_401658 := by decide
  rcases family_descends (prefixWord ++ tailWord_401658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401688 : List Nat := [2, 1, 2, 3, 1, 2, 4, 2, 1, 4]
def baseStart_401688 : Nat := 118140960795 + 401688 * 2 ^ 59
def prefixEnd_401688 : Nat := 4983230072969 + 3 ^ 40 * 401688 * 2
def baseEnd_401688 : Nat := 137506011428886418368451

theorem tailTrace_401688 : CollatzResearch.WordTrace tailWord_401688 prefixEnd_401688 137506011428886418368451 := by
  unfold tailWord_401688
  simp only [CollatzResearch.WordTrace]
  refine ⟨7325382484380226846878859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9767176645840302462505145 7325382484380226846878859)
  ·
    refine ⟨10988073726570340270318289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7325382484380226846878859 10988073726570340270318289)
    ·
      refine ⟨8241055294927755202738717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10988073726570340270318289 8241055294927755202738717)
      ·
        refine ⟨3090395735597908201027019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8241055294927755202738717 3090395735597908201027019)
        ·
          refine ⟨4635593603396862301540529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3090395735597908201027019 4635593603396862301540529)
          ·
            refine ⟨3476695202547646726155397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4635593603396862301540529 3476695202547646726155397)
            ·
              refine ⟨651880350477683761154137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3476695202547646726155397 651880350477683761154137)
              ·
                refine ⟨488910262858262820865603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 651880350477683761154137 488910262858262820865603)
                ·
                  refine ⟨733365394287394231298405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 488910262858262820865603 733365394287394231298405)
                  ·
                    refine ⟨137506011428886418368451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 733365394287394231298405 137506011428886418368451)
                    ·
                      rfl

theorem cell22_401688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_401688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401688 prefixEnd_401688 := by exact prefixLift 401688
  have htrace : WordTrace (prefixWord ++ tailWord_401688) baseStart_401688 baseEnd_401688 := by
    simpa [prefixWord, tailWord_401688, baseEnd_401688] using wordTrace_append hprefix tailTrace_401688
  have hstable : (prefixWord ++ tailWord_401688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401688).length < 2 ^ (prefixWord ++ tailWord_401688).sum := by decide
  have hdescent : baseEnd_401688 < baseStart_401688 := by decide
  rcases family_descends (prefixWord ++ tailWord_401688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401746 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 2, 7]
def baseStart_401746 : Nat := 118140960795 + 401746 * 2 ^ 59
def prefixEnd_401746 : Nat := 4983230072969 + 3 ^ 40 * 401746 * 2
def baseEnd_401746 : Nat := 137525866014193600418273

theorem tailTrace_401746 : CollatzResearch.WordTrace tailWord_401746 prefixEnd_401746 137525866014193600418273 := by
  unfold tailWord_401746
  simp only [CollatzResearch.WordTrace]
  refine ⟨3663220100637582399842273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9768586935033553066246061 3663220100637582399842273)
  ·
    refine ⟨2747415075478186799881705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3663220100637582399842273 2747415075478186799881705)
    ·
      refine ⟨2060561306608640099911279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2747415075478186799881705 2060561306608640099911279)
      ·
        refine ⟨3090841959912960149866919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2060561306608640099911279 3090841959912960149866919)
        ·
          refine ⟨4636262939869440224800379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3090841959912960149866919 4636262939869440224800379)
          ·
            refine ⟨6954394409804160337200569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4636262939869440224800379 6954394409804160337200569)
            ·
              refine ⟨5215795807353120252900427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6954394409804160337200569 5215795807353120252900427)
              ·
                refine ⟨7823693711029680379350641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5215795807353120252900427 7823693711029680379350641)
                ·
                  refine ⟨5867770283272260284512981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7823693711029680379350641 5867770283272260284512981)
                  ·
                    refine ⟨137525866014193600418273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5867770283272260284512981 137525866014193600418273)
                    ·
                      rfl

theorem cell22_401746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_401746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401746 prefixEnd_401746 := by exact prefixLift 401746
  have htrace : WordTrace (prefixWord ++ tailWord_401746) baseStart_401746 baseEnd_401746 := by
    simpa [prefixWord, tailWord_401746, baseEnd_401746] using wordTrace_append hprefix tailTrace_401746
  have hstable : (prefixWord ++ tailWord_401746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401746).length < 2 ^ (prefixWord ++ tailWord_401746).sum := by decide
  have hdescent : baseEnd_401746 < baseStart_401746 := by decide
  rcases family_descends (prefixWord ++ tailWord_401746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401782 : List Nat := [5, 1, 1, 4, 1, 2, 1, 7]
def baseStart_401782 : Nat := 118140960795 + 401782 * 2 ^ 59
def prefixEnd_401782 : Nat := 4983230072969 + 3 ^ 40 * 401782 * 2
def baseEnd_401782 : Nat := 15282021061100167390907

theorem tailTrace_401782 : CollatzResearch.WordTrace tailWord_401782 prefixEnd_401782 15282021061100167390907 := by
  unfold tailWord_401782
  simp only [CollatzResearch.WordTrace]
  refine ⟨915887089401244234229975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9769462286946605165119733 915887089401244234229975)
  ·
    refine ⟨1373830634101866351344963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 915887089401244234229975 1373830634101866351344963)
    ·
      refine ⟨2060745951152799527017445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1373830634101866351344963 2060745951152799527017445)
      ·
        refine ⟨386389865841149911315771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2060745951152799527017445 386389865841149911315771)
        ·
          refine ⟨579584798761724866973657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386389865841149911315771 579584798761724866973657)
          ·
            refine ⟨434688599071293650230243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 579584798761724866973657 434688599071293650230243)
            ·
              refine ⟨652032898606940475345365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434688599071293650230243 652032898606940475345365)
              ·
                refine ⟨15282021061100167390907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 652032898606940475345365 15282021061100167390907)
                ·
                  rfl

theorem cell22_401782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_401782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401782 prefixEnd_401782 := by exact prefixLift 401782
  have htrace : WordTrace (prefixWord ++ tailWord_401782) baseStart_401782 baseEnd_401782 := by
    simpa [prefixWord, tailWord_401782, baseEnd_401782] using wordTrace_append hprefix tailTrace_401782
  have hstable : (prefixWord ++ tailWord_401782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401782).length < 2 ^ (prefixWord ++ tailWord_401782).sum := by decide
  have hdescent : baseEnd_401782 < baseStart_401782 := by decide
  rcases family_descends (prefixWord ++ tailWord_401782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401791 : List Nat := [1, 1, 2, 2, 1, 1, 2, 5, 2, 5]
def baseStart_401791 : Nat := 118140960795 + 401791 * 2 ^ 59
def prefixEnd_401791 : Nat := 4983230072969 + 3 ^ 40 * 401791 * 2
def baseEnd_401791 : Nat := 137541270433828483043135

theorem tailTrace_401791 : CollatzResearch.WordTrace tailWord_401791 prefixEnd_401791 137541270433828483043135 := by
  unfold tailWord_401791
  simp only [CollatzResearch.WordTrace]
  refine ⟨14654521687387302284757227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9769681124924868189838151 14654521687387302284757227)
  ·
    refine ⟨21981782531080953427135841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14654521687387302284757227 21981782531080953427135841)
    ·
      refine ⟨16486336898310715070351881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21981782531080953427135841 16486336898310715070351881)
      ·
        refine ⟨12364752673733036302763911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16486336898310715070351881 12364752673733036302763911)
        ·
          refine ⟨18547129010599554454145867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12364752673733036302763911 18547129010599554454145867)
          ·
            refine ⟨27820693515899331681218801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18547129010599554454145867 27820693515899331681218801)
            ·
              refine ⟨20865520136924498760914101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27820693515899331681218801 20865520136924498760914101)
              ·
                refine ⟨1956142512836671758835697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20865520136924498760914101 1956142512836671758835697)
                ·
                  refine ⟨1467106884627503819126773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1956142512836671758835697 1467106884627503819126773)
                  ·
                    refine ⟨137541270433828483043135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1467106884627503819126773 137541270433828483043135)
                    ·
                      rfl

theorem cell22_401791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 5].length) (baseStart_401791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401791 prefixEnd_401791 := by exact prefixLift 401791
  have htrace : WordTrace (prefixWord ++ tailWord_401791) baseStart_401791 baseEnd_401791 := by
    simpa [prefixWord, tailWord_401791, baseEnd_401791] using wordTrace_append hprefix tailTrace_401791
  have hstable : (prefixWord ++ tailWord_401791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401791).length < 2 ^ (prefixWord ++ tailWord_401791).sum := by decide
  have hdescent : baseEnd_401791 < baseStart_401791 := by decide
  rcases family_descends (prefixWord ++ tailWord_401791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401885 : List Nat := [1, 4, 3, 1, 1, 1, 3, 2, 2, 4]
def baseStart_401885 : Nat := 118140960795 + 401885 * 2 ^ 59
def prefixEnd_401885 : Nat := 4983230072969 + 3 ^ 40 * 401885 * 2
def baseEnd_401885 : Nat := 137573448554843571192847

theorem tailTrace_401885 : CollatzResearch.WordTrace tailWord_401885 prefixEnd_401885 137573448554843571192847 := by
  unfold tailWord_401885
  simp only [CollatzResearch.WordTrace]
  refine ⟨14657950149046756338679109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9771966766031170892452739 14657950149046756338679109)
  ·
    refine ⟨2748365652946266813502333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14657950149046756338679109 2748365652946266813502333)
    ·
      refine ⟨1030637119854850055063375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2748365652946266813502333 1030637119854850055063375)
      ·
        refine ⟨1545955679782275082595063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1030637119854850055063375 1545955679782275082595063)
        ·
          refine ⟨2318933519673412623892595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1545955679782275082595063 2318933519673412623892595)
          ·
            refine ⟨3478400279510118935838893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2318933519673412623892595 3478400279510118935838893)
            ·
              refine ⟨1304400104816294600939585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3478400279510118935838893 1304400104816294600939585)
              ·
                refine ⟨978300078612220950704689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1304400104816294600939585 978300078612220950704689)
                ·
                  refine ⟨733725058959165713028517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 978300078612220950704689 733725058959165713028517)
                  ·
                    refine ⟨137573448554843571192847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 733725058959165713028517 137573448554843571192847)
                    ·
                      rfl

theorem cell22_401885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_401885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401885 prefixEnd_401885 := by exact prefixLift 401885
  have htrace : WordTrace (prefixWord ++ tailWord_401885) baseStart_401885 baseEnd_401885 := by
    simpa [prefixWord, tailWord_401885, baseEnd_401885] using wordTrace_append hprefix tailTrace_401885
  have hstable : (prefixWord ++ tailWord_401885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401885).length < 2 ^ (prefixWord ++ tailWord_401885).sum := by decide
  have hdescent : baseEnd_401885 < baseStart_401885 := by decide
  rcases family_descends (prefixWord ++ tailWord_401885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401949 : List Nat := [1, 4, 2, 2, 1, 3, 1, 4, 1, 3]
def baseStart_401949 : Nat := 118140960795 + 401949 * 2 ^ 59
def prefixEnd_401949 : Nat := 4983230072969 + 3 ^ 40 * 401949 * 2
def baseEnd_401949 : Nat := 137595357062768737592651

theorem tailTrace_401949 : CollatzResearch.WordTrace tailWord_401949 prefixEnd_401949 137595357062768737592651 := by
  unfold tailWord_401949
  simp only [CollatzResearch.WordTrace]
  refine ⟨14660284420814895269008901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9773522947209930179339267 14660284420814895269008901)
  ·
    refine ⟨2748803328902792862939169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14660284420814895269008901 2748803328902792862939169)
    ·
      refine ⟨2061602496677094647204377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2748803328902792862939169 2061602496677094647204377)
      ·
        refine ⟨1546201872507820985403283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2061602496677094647204377 1546201872507820985403283)
        ·
          refine ⟨2319302808761731478104925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1546201872507820985403283 2319302808761731478104925)
          ·
            refine ⟨869738553285649304289347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2319302808761731478104925 869738553285649304289347)
            ·
              refine ⟨1304607829928473956434021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869738553285649304289347 1304607829928473956434021)
              ·
                refine ⟨244613968111588866831379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1304607829928473956434021 244613968111588866831379)
                ·
                  refine ⟨366920952167383300247069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244613968111588866831379 366920952167383300247069)
                  ·
                    refine ⟨137595357062768737592651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 366920952167383300247069 137595357062768737592651)
                    ·
                      rfl

theorem cell22_401949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_401949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401949 prefixEnd_401949 := by exact prefixLift 401949
  have htrace : WordTrace (prefixWord ++ tailWord_401949) baseStart_401949 baseEnd_401949 := by
    simpa [prefixWord, tailWord_401949, baseEnd_401949] using wordTrace_append hprefix tailTrace_401949
  have hstable : (prefixWord ++ tailWord_401949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401949).length < 2 ^ (prefixWord ++ tailWord_401949).sum := by decide
  have hdescent : baseEnd_401949 < baseStart_401949 := by decide
  rcases family_descends (prefixWord ++ tailWord_401949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401960 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 1, 7]
def baseStart_401960 : Nat := 118140960795 + 401960 * 2 ^ 59
def prefixEnd_401960 : Nat := 4983230072969 + 3 ^ 40 * 401960 * 2
def baseEnd_401960 : Nat := 137599122587568375567617

theorem tailTrace_401960 : CollatzResearch.WordTrace tailWord_401960 prefixEnd_401960 137599122587568375567617 := by
  unfold tailWord_401960
  simp only [CollatzResearch.WordTrace]
  refine ⟨7330342811887522073829667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9773790415850029431772889 7330342811887522073829667)
  ·
    refine ⟨10995514217831283110744501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7330342811887522073829667 10995514217831283110744501)
    ·
      refine ⟨1030829457921682791632297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10995514217831283110744501 1030829457921682791632297)
      ·
        refine ⟨773122093441262093724223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1030829457921682791632297 773122093441262093724223)
        ·
          refine ⟨1159683140161893140586335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 773122093441262093724223 1159683140161893140586335)
          ·
            refine ⟨1739524710242839710879503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1159683140161893140586335 1739524710242839710879503)
            ·
              refine ⟨2609287065364259566319255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1739524710242839710879503 2609287065364259566319255)
              ·
                refine ⟨3913930598046389349478883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2609287065364259566319255 3913930598046389349478883)
                ·
                  refine ⟨5870895897069584024218325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3913930598046389349478883 5870895897069584024218325)
                  ·
                    refine ⟨137599122587568375567617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5870895897069584024218325 137599122587568375567617)
                    ·
                      rfl

theorem cell22_401960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_401960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401960 prefixEnd_401960 := by exact prefixLift 401960
  have htrace : WordTrace (prefixWord ++ tailWord_401960) baseStart_401960 baseEnd_401960 := by
    simpa [prefixWord, tailWord_401960, baseEnd_401960] using wordTrace_append hprefix tailTrace_401960
  have hstable : (prefixWord ++ tailWord_401960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401960).length < 2 ^ (prefixWord ++ tailWord_401960).sum := by decide
  have hdescent : baseEnd_401960 < baseStart_401960 := by decide
  rcases family_descends (prefixWord ++ tailWord_401960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401975 : List Nat := [1, 1, 3, 1, 2, 3, 2, 4, 1, 4]
def baseStart_401975 : Nat := 118140960795 + 401975 * 2 ^ 59
def prefixEnd_401975 : Nat := 4983230072969 + 3 ^ 40 * 401975 * 2
def baseEnd_401975 : Nat := 137604257394113336442571

theorem tailTrace_401975 : CollatzResearch.WordTrace tailWord_401975 prefixEnd_401975 137604257394113336442571 := by
  unfold tailWord_401975
  simp only [CollatzResearch.WordTrace]
  refine ⟨14661232718720701709455379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9774155145813801139636919 14661232718720701709455379)
  ·
    refine ⟨21991849078081052564183069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14661232718720701709455379 21991849078081052564183069)
    ·
      refine ⟨8246943404280394711568651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21991849078081052564183069 8246943404280394711568651)
      ·
        refine ⟨12370415106420592067352977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8246943404280394711568651 12370415106420592067352977)
        ·
          refine ⟨9277811329815444050514733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12370415106420592067352977 9277811329815444050514733)
          ·
            refine ⟨3479179248680791518943025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9277811329815444050514733 3479179248680791518943025)
            ·
              refine ⟨2609384436510593639207269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3479179248680791518943025 2609384436510593639207269)
              ·
                refine ⟨489259581845736307351363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2609384436510593639207269 489259581845736307351363)
                ·
                  refine ⟨733889372768604461027045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 489259581845736307351363 733889372768604461027045)
                  ·
                    refine ⟨137604257394113336442571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 733889372768604461027045 137604257394113336442571)
                    ·
                      rfl

theorem cell22_401975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_401975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_401975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_401975 prefixEnd_401975 := by exact prefixLift 401975
  have htrace : WordTrace (prefixWord ++ tailWord_401975) baseStart_401975 baseEnd_401975 := by
    simpa [prefixWord, tailWord_401975, baseEnd_401975] using wordTrace_append hprefix tailTrace_401975
  have hstable : (prefixWord ++ tailWord_401975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401975).length < 2 ^ (prefixWord ++ tailWord_401975).sum := by decide
  have hdescent : baseEnd_401975 < baseStart_401975 := by decide
  rcases family_descends (prefixWord ++ tailWord_401975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402157 : List Nat := [1, 5, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_402157 : Nat := 118140960795 + 402157 * 2 ^ 59
def prefixEnd_402157 : Nat := 4983230072969 + 3 ^ 40 * 402157 * 2
def baseEnd_402157 : Nat := 137666559713525528392013

theorem tailTrace_402157 : CollatzResearch.WordTrace tailWord_402157 prefixEnd_402157 137666559713525528392013 := by
  unfold tailWord_402157
  simp only [CollatzResearch.WordTrace]
  refine ⟨14667870804061346792580725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9778580536040897861720483 14667870804061346792580725)
  ·
    refine ⟨1375112887880751261804443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14667870804061346792580725 1375112887880751261804443)
    ·
      refine ⟨2062669331821126892706665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1375112887880751261804443 2062669331821126892706665)
      ·
        refine ⟨1547001998865845169529999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2062669331821126892706665 1547001998865845169529999)
        ·
          refine ⟨2320502998298767754294999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1547001998865845169529999 2320502998298767754294999)
          ·
            refine ⟨3480754497448151631442499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320502998298767754294999 3480754497448151631442499)
            ·
              refine ⟨5221131746172227447163749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3480754497448151631442499 5221131746172227447163749)
              ·
                refine ⟨978962202407292646343203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5221131746172227447163749 978962202407292646343203)
                ·
                  refine ⟨1468443303610938969514805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 978962202407292646343203 1468443303610938969514805)
                  ·
                    refine ⟨137666559713525528392013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1468443303610938969514805 137666559713525528392013)
                    ·
                      rfl

theorem cell22_402157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_402157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402157 prefixEnd_402157 := by exact prefixLift 402157
  have htrace : WordTrace (prefixWord ++ tailWord_402157) baseStart_402157 baseEnd_402157 := by
    simpa [prefixWord, tailWord_402157, baseEnd_402157] using wordTrace_append hprefix tailTrace_402157
  have hstable : (prefixWord ++ tailWord_402157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402157).length < 2 ^ (prefixWord ++ tailWord_402157).sum := by decide
  have hdescent : baseEnd_402157 < baseStart_402157 := by decide
  rcases family_descends (prefixWord ++ tailWord_402157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402159 : List Nat := [1, 1, 2, 1, 5, 3, 2, 3, 4]
def baseStart_402159 : Nat := 118140960795 + 402159 * 2 ^ 59
def prefixEnd_402159 : Nat := 4983230072969 + 3 ^ 40 * 402159 * 2
def baseEnd_402159 : Nat := 45889081451466063280669

theorem tailTrace_402159 : CollatzResearch.WordTrace tailWord_402159 prefixEnd_402159 45889081451466063280669 := by
  unfold tailWord_402159
  simp only [CollatzResearch.WordTrace]
  refine ⟨14667943750054101134153531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9778629166702734089435687 14667943750054101134153531)
  ·
    refine ⟨22001915625081151701230297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14667943750054101134153531 22001915625081151701230297)
    ·
      refine ⟨16501436718810863775922723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22001915625081151701230297 16501436718810863775922723)
      ·
        refine ⟨24752155078216295663884085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16501436718810863775922723 24752155078216295663884085)
        ·
          refine ⟨2320514538582777718489133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24752155078216295663884085 2320514538582777718489133)
          ·
            refine ⟨870192951968541644433425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2320514538582777718489133 870192951968541644433425)
            ·
              refine ⟨652644713976406233325069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 870192951968541644433425 652644713976406233325069)
              ·
                refine ⟨244741767741152337496901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 652644713976406233325069 244741767741152337496901)
                ·
                  refine ⟨45889081451466063280669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 244741767741152337496901 45889081451466063280669)
                  ·
                    rfl

theorem cell22_402159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3, 4].length) (baseStart_402159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402159 prefixEnd_402159 := by exact prefixLift 402159
  have htrace : WordTrace (prefixWord ++ tailWord_402159) baseStart_402159 baseEnd_402159 := by
    simpa [prefixWord, tailWord_402159, baseEnd_402159] using wordTrace_append hprefix tailTrace_402159
  have hstable : (prefixWord ++ tailWord_402159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402159).length < 2 ^ (prefixWord ++ tailWord_402159).sum := by decide
  have hdescent : baseEnd_402159 < baseStart_402159 := by decide
  rcases family_descends (prefixWord ++ tailWord_402159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402165 : List Nat := [1, 3, 6, 1, 2, 1, 1, 2, 5]
def baseStart_402165 : Nat := 118140960795 + 402165 * 2 ^ 59
def prefixEnd_402165 : Nat := 4983230072969 + 3 ^ 40 * 402165 * 2
def baseEnd_402165 : Nat := 45889766092338724730663

theorem tailTrace_402165 : CollatzResearch.WordTrace tailWord_402165 prefixEnd_402165 45889766092338724730663 := by
  unfold tailWord_402165
  simp only [CollatzResearch.WordTrace]
  refine ⟨14668162588032364158871949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9778775058688242772581299 14668162588032364158871949)
  ·
    refine ⟨5500560970512136559576981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14668162588032364158871949 5500560970512136559576981)
    ·
      refine ⟨257838795492756401230171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5500560970512136559576981 257838795492756401230171)
      ·
        refine ⟨386758193239134601845257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257838795492756401230171 386758193239134601845257)
        ·
          refine ⟨290068644929350951383943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386758193239134601845257 290068644929350951383943)
          ·
            refine ⟨435102967394026427075915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290068644929350951383943 435102967394026427075915)
            ·
              refine ⟨652654451091039640613873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 435102967394026427075915 652654451091039640613873)
              ·
                refine ⟨489490838318279730460405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 652654451091039640613873 489490838318279730460405)
                ·
                  refine ⟨45889766092338724730663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 489490838318279730460405 45889766092338724730663)
                  ·
                    rfl

theorem cell22_402165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 5].length) (baseStart_402165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402165 prefixEnd_402165 := by exact prefixLift 402165
  have htrace : WordTrace (prefixWord ++ tailWord_402165) baseStart_402165 baseEnd_402165 := by
    simpa [prefixWord, tailWord_402165, baseEnd_402165] using wordTrace_append hprefix tailTrace_402165
  have hstable : (prefixWord ++ tailWord_402165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402165).length < 2 ^ (prefixWord ++ tailWord_402165).sum := by decide
  have hdescent : baseEnd_402165 < baseStart_402165 := by decide
  rcases family_descends (prefixWord ++ tailWord_402165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402204 : List Nat := [2, 2, 3, 1, 1, 5, 2, 6]
def baseStart_402204 : Nat := 118140960795 + 402204 * 2 ^ 59
def prefixEnd_402204 : Nat := 4983230072969 + 3 ^ 40 * 402204 * 2
def baseEnd_402204 : Nat := 15298072086003674718541

theorem tailTrace_402204 : CollatzResearch.WordTrace tailWord_402204 prefixEnd_402204 15298072086003674718541 := by
  unfold tailWord_402204
  simp only [CollatzResearch.WordTrace]
  refine ⟨7334792517445536909770833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9779723356594049213027777 7334792517445536909770833)
  ·
    refine ⟨5501094388084152682328125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7334792517445536909770833 5501094388084152682328125)
    ·
      refine ⟨2062910395531557255873047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5501094388084152682328125 2062910395531557255873047)
      ·
        refine ⟨3094365593297335883809571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2062910395531557255873047 3094365593297335883809571)
        ·
          refine ⟨4641548389946003825714357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3094365593297335883809571 4641548389946003825714357)
          ·
            refine ⟨435145161557437858660721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4641548389946003825714357 435145161557437858660721)
            ·
              refine ⟨326358871168078393995541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435145161557437858660721 326358871168078393995541)
              ·
                refine ⟨15298072086003674718541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 326358871168078393995541 15298072086003674718541)
                ·
                  rfl

theorem cell22_402204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 6].length) (baseStart_402204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402204 prefixEnd_402204 := by exact prefixLift 402204
  have htrace : WordTrace (prefixWord ++ tailWord_402204) baseStart_402204 baseEnd_402204 := by
    simpa [prefixWord, tailWord_402204, baseEnd_402204] using wordTrace_append hprefix tailTrace_402204
  have hstable : (prefixWord ++ tailWord_402204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402204).length < 2 ^ (prefixWord ++ tailWord_402204).sum := by decide
  have hdescent : baseEnd_402204 < baseStart_402204 := by decide
  rcases family_descends (prefixWord ++ tailWord_402204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402221 : List Nat := [1, 5, 3, 2, 1, 2, 8]
def baseStart_402221 : Nat := 118140960795 + 402221 * 2 ^ 59
def prefixEnd_402221 : Nat := 4983230072969 + 3 ^ 40 * 402221 * 2
def baseEnd_402221 : Nat := 5099572897090766473771

theorem tailTrace_402221 : CollatzResearch.WordTrace tailWord_402221 prefixEnd_402221 5099572897090766473771 := by
  unfold tailWord_402221
  simp only [CollatzResearch.WordTrace]
  refine ⟨14670205075829485722910517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9780136717219657148607011 14670205075829485722910517)
  ·
    refine ⟨1375331725859014286522861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14670205075829485722910517 1375331725859014286522861)
    ·
      refine ⟨515749397197130357446073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1375331725859014286522861 515749397197130357446073)
      ·
        refine ⟨386812047897847768084555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 515749397197130357446073 386812047897847768084555)
        ·
          refine ⟨580218071846771652126833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386812047897847768084555 580218071846771652126833)
          ·
            refine ⟨435163553885078739095125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 580218071846771652126833 435163553885078739095125)
            ·
              refine ⟨5099572897090766473771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 435163553885078739095125 5099572897090766473771)
              ·
                rfl

theorem cell22_402221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 8].length) (baseStart_402221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402221 prefixEnd_402221 := by exact prefixLift 402221
  have htrace : WordTrace (prefixWord ++ tailWord_402221) baseStart_402221 baseEnd_402221 := by
    simpa [prefixWord, tailWord_402221, baseEnd_402221] using wordTrace_append hprefix tailTrace_402221
  have hstable : (prefixWord ++ tailWord_402221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402221).length < 2 ^ (prefixWord ++ tailWord_402221).sum := by decide
  have hdescent : baseEnd_402221 < baseStart_402221 := by decide
  rcases family_descends (prefixWord ++ tailWord_402221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402232 : List Nat := [2, 1, 2, 1, 3, 2, 2, 4, 5]
def baseStart_402232 : Nat := 118140960795 + 402232 * 2 ^ 59
def prefixEnd_402232 : Nat := 4983230072969 + 3 ^ 40 * 402232 * 2
def baseEnd_402232 : Nat := 45897411248750110922261

theorem tailTrace_402232 : CollatzResearch.WordTrace tailWord_402232 prefixEnd_402232 45897411248750110922261 := by
  unfold tailWord_402232
  simp only [CollatzResearch.WordTrace]
  refine ⟨7335303139394817300780475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9780404185859756401040633 7335303139394817300780475)
  ·
    refine ⟨11002954709092225951170713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7335303139394817300780475 11002954709092225951170713)
    ·
      refine ⟨8252216031819169463378035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11002954709092225951170713 8252216031819169463378035)
      ·
        refine ⟨12378324047728754195067053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8252216031819169463378035 12378324047728754195067053)
        ·
          refine ⟨4641871517898282823150145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12378324047728754195067053 4641871517898282823150145)
          ·
            refine ⟨3481403638423712117362609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4641871517898282823150145 3481403638423712117362609)
            ·
              refine ⟨2611052728817784088021957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3481403638423712117362609 2611052728817784088021957)
              ·
                refine ⟨489572386653334516504117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2611052728817784088021957 489572386653334516504117)
                ·
                  refine ⟨45897411248750110922261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 489572386653334516504117 45897411248750110922261)
                  ·
                    rfl

theorem cell22_402232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 5].length) (baseStart_402232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402232 prefixEnd_402232 := by exact prefixLift 402232
  have htrace : WordTrace (prefixWord ++ tailWord_402232) baseStart_402232 baseEnd_402232 := by
    simpa [prefixWord, tailWord_402232, baseEnd_402232] using wordTrace_append hprefix tailTrace_402232
  have hstable : (prefixWord ++ tailWord_402232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402232).length < 2 ^ (prefixWord ++ tailWord_402232).sum := by decide
  have hdescent : baseEnd_402232 < baseStart_402232 := by decide
  rcases family_descends (prefixWord ++ tailWord_402232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402249 : List Nat := [1, 2, 1, 1, 2, 5, 4, 1, 5]
def baseStart_402249 : Nat := 118140960795 + 402249 * 2 ^ 59
def prefixEnd_402249 : Nat := 4983230072969 + 3 ^ 40 * 402249 * 2
def baseEnd_402249 : Nat := 45899351064555985030577

theorem tailTrace_402249 : CollatzResearch.WordTrace tailWord_402249 prefixEnd_402249 45899351064555985030577 := by
  unfold tailWord_402249
  simp only [CollatzResearch.WordTrace]
  refine ⟨14671226319728046504929801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9780817546485364336619867 14671226319728046504929801)
  ·
    refine ⟨11003419739796034878697351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14671226319728046504929801 11003419739796034878697351)
    ·
      refine ⟨16505129609694052318046027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11003419739796034878697351 16505129609694052318046027)
      ·
        refine ⟨24757694414541078477069041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16505129609694052318046027 24757694414541078477069041)
        ·
          refine ⟨18568270810905808857801781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24757694414541078477069041 18568270810905808857801781)
          ·
            refine ⟨1740775388522419580418917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18568270810905808857801781 1740775388522419580418917)
            ·
              refine ⟨326395385347953671328547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1740775388522419580418917 326395385347953671328547)
              ·
                refine ⟨489593078021930506992821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 326395385347953671328547 489593078021930506992821)
                ·
                  refine ⟨45899351064555985030577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 489593078021930506992821 45899351064555985030577)
                  ·
                    rfl

theorem cell22_402249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 5].length) (baseStart_402249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402249 prefixEnd_402249 := by exact prefixLift 402249
  have htrace : WordTrace (prefixWord ++ tailWord_402249) baseStart_402249 baseEnd_402249 := by
    simpa [prefixWord, tailWord_402249, baseEnd_402249] using wordTrace_append hprefix tailTrace_402249
  have hstable : (prefixWord ++ tailWord_402249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402249).length < 2 ^ (prefixWord ++ tailWord_402249).sum := by decide
  have hdescent : baseEnd_402249 < baseStart_402249 := by decide
  rcases family_descends (prefixWord ++ tailWord_402249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402307 : List Nat := [1, 1, 1, 3, 4, 1, 2, 2, 1, 6]
def baseStart_402307 : Nat := 118140960795 + 402307 * 2 ^ 59
def prefixEnd_402307 : Nat := 4983230072969 + 3 ^ 40 * 402307 * 2
def baseEnd_402307 : Nat := 137717907778975137141553

theorem tailTrace_402307 : CollatzResearch.WordTrace tailWord_402307 prefixEnd_402307 137717907778975137141553 := by
  unfold tailWord_402307
  simp only [CollatzResearch.WordTrace]
  refine ⟨14673341753517922410541175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9782227835678614940360783 14673341753517922410541175)
  ·
    refine ⟨22010012630276883615811763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14673341753517922410541175 22010012630276883615811763)
    ·
      refine ⟨33015018945415325423717645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22010012630276883615811763 33015018945415325423717645)
      ·
        refine ⟨12380632104530747033894117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33015018945415325423717645 12380632104530747033894117)
        ·
          refine ⟨2321368519599515068855147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12380632104530747033894117 2321368519599515068855147)
          ·
            refine ⟨3482052779399272603282721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2321368519599515068855147 3482052779399272603282721)
            ·
              refine ⟨2611539584549454452462041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3482052779399272603282721 2611539584549454452462041)
              ·
                refine ⟨1958654688412090839346531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2611539584549454452462041 1958654688412090839346531)
                ·
                  refine ⟨2937982032618136259019797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1958654688412090839346531 2937982032618136259019797)
                  ·
                    refine ⟨137717907778975137141553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2937982032618136259019797 137717907778975137141553)
                    ·
                      rfl

theorem cell22_402307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 6].length) (baseStart_402307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402307 prefixEnd_402307 := by exact prefixLift 402307
  have htrace : WordTrace (prefixWord ++ tailWord_402307) baseStart_402307 baseEnd_402307 := by
    simpa [prefixWord, tailWord_402307, baseEnd_402307] using wordTrace_append hprefix tailTrace_402307
  have hstable : (prefixWord ++ tailWord_402307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402307).length < 2 ^ (prefixWord ++ tailWord_402307).sum := by decide
  have hdescent : baseEnd_402307 < baseStart_402307 := by decide
  rcases family_descends (prefixWord ++ tailWord_402307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402309 : List Nat := [1, 3, 1, 1, 3, 4, 2, 1, 1, 5]
def baseStart_402309 : Nat := 118140960795 + 402309 * 2 ^ 59
def prefixEnd_402309 : Nat := 4983230072969 + 3 ^ 40 * 402309 * 2
def baseEnd_402309 : Nat := 137718592419847798591547

theorem tailTrace_402309 : CollatzResearch.WordTrace tailWord_402309 prefixEnd_402309 137718592419847798591547 := by
  unfold tailWord_402309
  simp only [CollatzResearch.WordTrace]
  refine ⟨14673414699510676752113981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9782276466340451168075987 14673414699510676752113981)
  ·
    refine ⟨5502530512316503782042743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14673414699510676752113981 5502530512316503782042743)
    ·
      refine ⟨8253795768474755673064115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5502530512316503782042743 8253795768474755673064115)
      ·
        refine ⟨12380693652712133509596173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8253795768474755673064115 12380693652712133509596173)
        ·
          refine ⟨4642760119767050066098565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12380693652712133509596173 4642760119767050066098565)
          ·
            refine ⟨870517522456321887393481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4642760119767050066098565 870517522456321887393481)
            ·
              refine ⟨652888141842241415545111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 870517522456321887393481 652888141842241415545111)
              ·
                refine ⟨979332212763362123317667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 652888141842241415545111 979332212763362123317667)
                ·
                  refine ⟨1468998319145043184976501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 979332212763362123317667 1468998319145043184976501)
                  ·
                    refine ⟨137718592419847798591547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1468998319145043184976501 137718592419847798591547)
                    ·
                      rfl

theorem cell22_402309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_402309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402309 prefixEnd_402309 := by exact prefixLift 402309
  have htrace : WordTrace (prefixWord ++ tailWord_402309) baseStart_402309 baseEnd_402309 := by
    simpa [prefixWord, tailWord_402309, baseEnd_402309] using wordTrace_append hprefix tailTrace_402309
  have hstable : (prefixWord ++ tailWord_402309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402309).length < 2 ^ (prefixWord ++ tailWord_402309).sum := by decide
  have hdescent : baseEnd_402309 < baseStart_402309 := by decide
  rcases family_descends (prefixWord ++ tailWord_402309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402324 : List Nat := [2, 4, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_402324 : Nat := 118140960795 + 402324 * 2 ^ 59
def prefixEnd_402324 : Nat := 4983230072969 + 3 ^ 40 * 402324 * 2
def baseEnd_402324 : Nat := 137723727226392759466501

theorem tailTrace_402324 : CollatzResearch.WordTrace tailWord_402324 prefixEnd_402324 137723727226392759466501 := by
  unfold tailWord_402324
  simp only [CollatzResearch.WordTrace]
  refine ⟨7336980897228167156955013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9782641196304222875940017 7336980897228167156955013)
  ·
    refine ⟨1375683918230281341929065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7336980897228167156955013 1375683918230281341929065)
    ·
      refine ⟨1031762938672711006446799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1375683918230281341929065 1031762938672711006446799)
      ·
        refine ⟨1547644408009066509670199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1031762938672711006446799 1547644408009066509670199)
        ·
          refine ⟨2321466612013599764505299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1547644408009066509670199 2321466612013599764505299)
          ·
            refine ⟨3482199918020399646757949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2321466612013599764505299 3482199918020399646757949)
            ·
              refine ⟨1305824969257649867534231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3482199918020399646757949 1305824969257649867534231)
              ·
                refine ⟨1958737453886474801301347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1305824969257649867534231 1958737453886474801301347)
                ·
                  refine ⟨2938106180829712201952021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1958737453886474801301347 2938106180829712201952021)
                  ·
                    refine ⟨137723727226392759466501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2938106180829712201952021 137723727226392759466501)
                    ·
                      rfl

theorem cell22_402324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_402324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402324 prefixEnd_402324 := by exact prefixLift 402324
  have htrace : WordTrace (prefixWord ++ tailWord_402324) baseStart_402324 baseEnd_402324 := by
    simpa [prefixWord, tailWord_402324, baseEnd_402324] using wordTrace_append hprefix tailTrace_402324
  have hstable : (prefixWord ++ tailWord_402324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402324).length < 2 ^ (prefixWord ++ tailWord_402324).sum := by decide
  have hdescent : baseEnd_402324 < baseStart_402324 := by decide
  rcases family_descends (prefixWord ++ tailWord_402324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402330 : List Nat := [3, 1, 1, 4, 4, 1, 2, 1, 1, 4]
def baseStart_402330 : Nat := 118140960795 + 402330 * 2 ^ 59
def prefixEnd_402330 : Nat := 4983230072969 + 3 ^ 40 * 402330 * 2
def baseEnd_402330 : Nat := 137725781149010743816483

theorem tailTrace_402330 : CollatzResearch.WordTrace tailWord_402330 prefixEnd_402330 137725781149010743816483 := by
  unfold tailWord_402330
  simp only [CollatzResearch.WordTrace]
  refine ⟨3668545158108649334657111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9782787088289731559085629 3668545158108649334657111)
  ·
    refine ⟨5502817737162974001985667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3668545158108649334657111 5502817737162974001985667)
    ·
      refine ⟨8254226605744461002978501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5502817737162974001985667 8254226605744461002978501)
      ·
        refine ⟨1547667488577086438058469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8254226605744461002978501 1547667488577086438058469)
        ·
          refine ⟨290187654108203707135963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1547667488577086438058469 290187654108203707135963)
          ·
            refine ⟨435281481162305560703945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290187654108203707135963 435281481162305560703945)
            ·
              refine ⟨326461110871729170527959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435281481162305560703945 326461110871729170527959)
              ·
                refine ⟨489691666307593755791939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 326461110871729170527959 489691666307593755791939)
                ·
                  refine ⟨734537499461390633687909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 489691666307593755791939 734537499461390633687909)
                  ·
                    refine ⟨137725781149010743816483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 734537499461390633687909 137725781149010743816483)
                    ·
                      rfl

theorem cell22_402330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 1, 4].length) (baseStart_402330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402330 prefixEnd_402330 := by exact prefixLift 402330
  have htrace : WordTrace (prefixWord ++ tailWord_402330) baseStart_402330 baseEnd_402330 := by
    simpa [prefixWord, tailWord_402330, baseEnd_402330] using wordTrace_append hprefix tailTrace_402330
  have hstable : (prefixWord ++ tailWord_402330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402330).length < 2 ^ (prefixWord ++ tailWord_402330).sum := by decide
  have hdescent : baseEnd_402330 < baseStart_402330 := by decide
  rcases family_descends (prefixWord ++ tailWord_402330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402405 : List Nat := [1, 3, 1, 6, 1, 2, 1, 1, 3, 3]
def baseStart_402405 : Nat := 118140960795 + 402405 * 2 ^ 59
def prefixEnd_402405 : Nat := 4983230072969 + 3 ^ 40 * 402405 * 2
def baseEnd_402405 : Nat := 137751455181735548191253

theorem tailTrace_402405 : CollatzResearch.WordTrace tailWord_402405 prefixEnd_402405 137751455181735548191253 := by
  unfold tailWord_402405
  simp only [CollatzResearch.WordTrace]
  refine ⟨14676916107162885147608669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9784610738108590098405779 14676916107162885147608669)
  ·
    refine ⟨5503843540186081930353251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14676916107162885147608669 5503843540186081930353251)
    ·
      refine ⟨8255765310279122895529877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5503843540186081930353251 8255765310279122895529877)
      ·
        refine ⟨386988998919333885727963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8255765310279122895529877 386988998919333885727963)
        ·
          refine ⟨580483498379000828591945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386988998919333885727963 580483498379000828591945)
          ·
            refine ⟨435362623784250621443959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 580483498379000828591945 435362623784250621443959)
            ·
              refine ⟨653043935676375932165939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 435362623784250621443959 653043935676375932165939)
              ·
                refine ⟨979565903514563898248909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 653043935676375932165939 979565903514563898248909)
                ·
                  refine ⟨367337213817961461843341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 979565903514563898248909 367337213817961461843341)
                  ·
                    refine ⟨137751455181735548191253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 367337213817961461843341 137751455181735548191253)
                    ·
                      rfl

theorem cell22_402405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 3, 3].length) (baseStart_402405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402405 prefixEnd_402405 := by exact prefixLift 402405
  have htrace : WordTrace (prefixWord ++ tailWord_402405) baseStart_402405 baseEnd_402405 := by
    simpa [prefixWord, tailWord_402405, baseEnd_402405] using wordTrace_append hprefix tailTrace_402405
  have hstable : (prefixWord ++ tailWord_402405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402405).length < 2 ^ (prefixWord ++ tailWord_402405).sum := by decide
  have hdescent : baseEnd_402405 < baseStart_402405 := by decide
  rcases family_descends (prefixWord ++ tailWord_402405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402418 : List Nat := [3, 2, 1, 5, 1, 1, 1, 3, 5]
def baseStart_402418 : Nat := 118140960795 + 402418 * 2 ^ 59
def prefixEnd_402418 : Nat := 4983230072969 + 3 ^ 40 * 402418 * 2
def baseEnd_402418 : Nat := 45918635115802615872071

theorem tailTrace_402418 : CollatzResearch.WordTrace tailWord_402418 prefixEnd_402418 45918635115802615872071 := by
  unfold tailWord_402418
  simp only [CollatzResearch.WordTrace]
  refine ⟨3669347564028947091957977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9784926837410525578554605 3669347564028947091957977)
  ·
    refine ⟨2752010673021710318968483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3669347564028947091957977 2752010673021710318968483)
    ·
      refine ⟨4128016009532565478452725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2752010673021710318968483 4128016009532565478452725)
      ·
        refine ⟨387001500893678013604943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4128016009532565478452725 387001500893678013604943)
        ·
          refine ⟨580502251340517020407415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387001500893678013604943 580502251340517020407415)
          ·
            refine ⟨870753377010775530611123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580502251340517020407415 870753377010775530611123)
            ·
              refine ⟨1306130065516163295916685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 870753377010775530611123 1306130065516163295916685)
              ·
                refine ⟨489798774568561235968757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1306130065516163295916685 489798774568561235968757)
                ·
                  refine ⟨45918635115802615872071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 489798774568561235968757 45918635115802615872071)
                  ·
                    rfl

theorem cell22_402418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_402418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402418 prefixEnd_402418 := by exact prefixLift 402418
  have htrace : WordTrace (prefixWord ++ tailWord_402418) baseStart_402418 baseEnd_402418 := by
    simpa [prefixWord, tailWord_402418, baseEnd_402418] using wordTrace_append hprefix tailTrace_402418
  have hstable : (prefixWord ++ tailWord_402418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402418).length < 2 ^ (prefixWord ++ tailWord_402418).sum := by decide
  have hdescent : baseEnd_402418 < baseStart_402418 := by decide
  rcases family_descends (prefixWord ++ tailWord_402418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402444 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 3, 5]
def baseStart_402444 : Nat := 118140960795 + 402444 * 2 ^ 59
def prefixEnd_402444 : Nat := 4983230072969 + 3 ^ 40 * 402444 * 2
def baseEnd_402444 : Nat := 137764805678752446466133

theorem tailTrace_402444 : CollatzResearch.WordTrace tailWord_402444 prefixEnd_402444 137764805678752446466133 := by
  unfold tailWord_402444
  simp only [CollatzResearch.WordTrace]
  refine ⟨7339169277010797404139193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9785559036014396538852257 7339169277010797404139193)
  ·
    refine ⟨5504376957758098053104395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7339169277010797404139193 5504376957758098053104395)
    ·
      refine ⟨8256565436637147079656593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5504376957758098053104395 8256565436637147079656593)
      ·
        refine ⟨6192424077477860309742445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8256565436637147079656593 6192424077477860309742445)
        ·
          refine ⟨2322159029054197616153417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6192424077477860309742445 2322159029054197616153417)
          ·
            refine ⟨1741619271790648212115063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2322159029054197616153417 1741619271790648212115063)
            ·
              refine ⟨2612428907685972318172595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1741619271790648212115063 2612428907685972318172595)
              ·
                refine ⟨3918643361528958477258893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2612428907685972318172595 3918643361528958477258893)
                ·
                  refine ⟨1469491260573359428972085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3918643361528958477258893 1469491260573359428972085)
                  ·
                    refine ⟨137764805678752446466133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1469491260573359428972085 137764805678752446466133)
                    ·
                      rfl

theorem cell22_402444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_402444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402444 prefixEnd_402444 := by exact prefixLift 402444
  have htrace : WordTrace (prefixWord ++ tailWord_402444) baseStart_402444 baseEnd_402444 := by
    simpa [prefixWord, tailWord_402444, baseEnd_402444] using wordTrace_append hprefix tailTrace_402444
  have hstable : (prefixWord ++ tailWord_402444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402444).length < 2 ^ (prefixWord ++ tailWord_402444).sum := by decide
  have hdescent : baseEnd_402444 < baseStart_402444 := by decide
  rcases family_descends (prefixWord ++ tailWord_402444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402463 : List Nat := [1, 1, 2, 4, 1, 3, 4, 2, 4]
def baseStart_402463 : Nat := 118140960795 + 402463 * 2 ^ 59
def prefixEnd_402463 : Nat := 4983230072969 + 3 ^ 40 * 402463 * 2
def baseEnd_402463 : Nat := 45923769922347576747025

theorem tailTrace_402463 : CollatzResearch.WordTrace tailWord_402463 prefixEnd_402463 45923769922347576747025 := by
  unfold tailWord_402463
  simp only [CollatzResearch.WordTrace]
  refine ⟨14679031540952761053220043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9786021027301840702146695 14679031540952761053220043)
  ·
    refine ⟨22018547311429141579830065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14679031540952761053220043 22018547311429141579830065)
    ·
      refine ⟨16513910483571856184872549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22018547311429141579830065 16513910483571856184872549)
      ·
        refine ⟨3096358215669723034663603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16513910483571856184872549 3096358215669723034663603)
        ·
          refine ⟨4644537323504584551995405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3096358215669723034663603 4644537323504584551995405)
          ·
            refine ⟨1741701496314219206998277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4644537323504584551995405 1741701496314219206998277)
            ·
              refine ⟨326569030558916101312177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1741701496314219206998277 326569030558916101312177)
              ·
                refine ⟨244926772919187075984133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326569030558916101312177 244926772919187075984133)
                ·
                  refine ⟨45923769922347576747025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 244926772919187075984133 45923769922347576747025)
                  ·
                    rfl

theorem cell22_402463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2, 4].length) (baseStart_402463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402463 prefixEnd_402463 := by exact prefixLift 402463
  have htrace : WordTrace (prefixWord ++ tailWord_402463) baseStart_402463 baseEnd_402463 := by
    simpa [prefixWord, tailWord_402463, baseEnd_402463] using wordTrace_append hprefix tailTrace_402463
  have hstable : (prefixWord ++ tailWord_402463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402463).length < 2 ^ (prefixWord ++ tailWord_402463).sum := by decide
  have hdescent : baseEnd_402463 < baseStart_402463 := by decide
  rcases family_descends (prefixWord ++ tailWord_402463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402478 : List Nat := [4, 1, 3, 1, 1, 1, 1, 5, 2, 3]
def baseStart_402478 : Nat := 118140960795 + 402478 * 2 ^ 59
def prefixEnd_402478 : Nat := 4983230072969 + 3 ^ 40 * 402478 * 2
def baseEnd_402478 : Nat := 137776444573587691116029

theorem tailTrace_402478 : CollatzResearch.WordTrace tailWord_402478 prefixEnd_402478 137776444573587691116029 := by
  unfold tailWord_402478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1834947329487302326877011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9786385757265612410010725 1834947329487302326877011)
  ·
    refine ⟨2752420994230953490315517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1834947329487302326877011 2752420994230953490315517)
    ·
      refine ⟨1032157872836607558868319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2752420994230953490315517 1032157872836607558868319)
      ·
        refine ⟨1548236809254911338302479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1032157872836607558868319 1548236809254911338302479)
        ·
          refine ⟨2322355213882367007453719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1548236809254911338302479 2322355213882367007453719)
          ·
            refine ⟨3483532820823550511180579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2322355213882367007453719 3483532820823550511180579)
            ·
              refine ⟨5225299231235325766770869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3483532820823550511180579 5225299231235325766770869)
              ·
                refine ⟨489871802928311790634769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5225299231235325766770869 489871802928311790634769)
                ·
                  refine ⟨367403852196233842976077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 489871802928311790634769 367403852196233842976077)
                  ·
                    refine ⟨137776444573587691116029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 367403852196233842976077 137776444573587691116029)
                    ·
                      rfl

theorem cell22_402478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_402478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402478 prefixEnd_402478 := by exact prefixLift 402478
  have htrace : WordTrace (prefixWord ++ tailWord_402478) baseStart_402478 baseEnd_402478 := by
    simpa [prefixWord, tailWord_402478, baseEnd_402478] using wordTrace_append hprefix tailTrace_402478
  have hstable : (prefixWord ++ tailWord_402478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402478).length < 2 ^ (prefixWord ++ tailWord_402478).sum := by decide
  have hdescent : baseEnd_402478 < baseStart_402478 := by decide
  rcases family_descends (prefixWord ++ tailWord_402478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402493 : List Nat := [1, 4, 1, 3, 1, 4, 1, 1, 2, 4]
def baseStart_402493 : Nat := 118140960795 + 402493 * 2 ^ 59
def prefixEnd_402493 : Nat := 4983230072969 + 3 ^ 40 * 402493 * 2
def baseEnd_402493 : Nat := 137781579380132651990983

theorem tailTrace_402493 : CollatzResearch.WordTrace tailWord_402493 prefixEnd_402493 137781579380132651990983 := by
  unfold tailWord_402493
  simp only [CollatzResearch.WordTrace]
  refine ⟨14680125730844076176812133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9786750487229384117874755 14680125730844076176812133)
  ·
    refine ⟨2752523574533264283152275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14680125730844076176812133 2752523574533264283152275)
    ·
      refine ⟨4128785361799896424728413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2752523574533264283152275 4128785361799896424728413)
      ·
        refine ⟨1548294510674961159273155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4128785361799896424728413 1548294510674961159273155)
        ·
          refine ⟨2322441766012441738909733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1548294510674961159273155 2322441766012441738909733)
          ·
            refine ⟨435457831127332826045575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2322441766012441738909733 435457831127332826045575)
            ·
              refine ⟨653186746690999239068363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 435457831127332826045575 653186746690999239068363)
              ·
                refine ⟨979780120036498858602545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 653186746690999239068363 979780120036498858602545)
                ·
                  refine ⟨734835090027374143951909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 979780120036498858602545 734835090027374143951909)
                  ·
                    refine ⟨137781579380132651990983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 734835090027374143951909 137781579380132651990983)
                    ·
                      rfl

theorem cell22_402493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_402493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402493 prefixEnd_402493 := by exact prefixLift 402493
  have htrace : WordTrace (prefixWord ++ tailWord_402493) baseStart_402493 baseEnd_402493 := by
    simpa [prefixWord, tailWord_402493, baseEnd_402493] using wordTrace_append hprefix tailTrace_402493
  have hstable : (prefixWord ++ tailWord_402493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402493).length < 2 ^ (prefixWord ++ tailWord_402493).sum := by decide
  have hdescent : baseEnd_402493 < baseStart_402493 := by decide
  rcases family_descends (prefixWord ++ tailWord_402493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402611 : List Nat := [1, 1, 1, 2, 3, 2, 3, 3, 2, 4]
def baseStart_402611 : Nat := 118140960795 + 402611 * 2 ^ 59
def prefixEnd_402611 : Nat := 4983230072969 + 3 ^ 40 * 402611 * 2
def baseEnd_402611 : Nat := 137821973191619677540621

theorem tailTrace_402611 : CollatzResearch.WordTrace tailWord_402611 prefixEnd_402611 137821973191619677540621 := by
  unfold tailWord_402611
  simp only [CollatzResearch.WordTrace]
  refine ⟨14684429544416582329607687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9789619696277721553071791 14684429544416582329607687)
  ·
    refine ⟨22026644316624873494411531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14684429544416582329607687 22026644316624873494411531)
    ·
      refine ⟨33039966474937310241617297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22026644316624873494411531 33039966474937310241617297)
      ·
        refine ⟨24779974856202982681212973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33039966474937310241617297 24779974856202982681212973)
        ·
          refine ⟨9292490571076118505454865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24779974856202982681212973 9292490571076118505454865)
          ·
            refine ⟨6969367928307088879091149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9292490571076118505454865 6969367928307088879091149)
            ·
              refine ⟨2613512973115158329659181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6969367928307088879091149 2613512973115158329659181)
              ·
                refine ⟨980067364918184373622193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2613512973115158329659181 980067364918184373622193)
                ·
                  refine ⟨735050523688638280216645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 980067364918184373622193 735050523688638280216645)
                  ·
                    refine ⟨137821973191619677540621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 735050523688638280216645 137821973191619677540621)
                    ·
                      rfl

theorem cell22_402611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 4].length) (baseStart_402611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402611 prefixEnd_402611 := by exact prefixLift 402611
  have htrace : WordTrace (prefixWord ++ tailWord_402611) baseStart_402611 baseEnd_402611 := by
    simpa [prefixWord, tailWord_402611, baseEnd_402611] using wordTrace_append hprefix tailTrace_402611
  have hstable : (prefixWord ++ tailWord_402611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402611).length < 2 ^ (prefixWord ++ tailWord_402611).sum := by decide
  have hdescent : baseEnd_402611 < baseStart_402611 := by decide
  rcases family_descends (prefixWord ++ tailWord_402611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402675 : List Nat := [1, 1, 1, 2, 2, 5, 1, 5, 1, 3]
def baseStart_402675 : Nat := 118140960795 + 402675 * 2 ^ 59
def prefixEnd_402675 : Nat := 4983230072969 + 3 ^ 40 * 402675 * 2
def baseEnd_402675 : Nat := 137843881699544843940425

theorem tailTrace_402675 : CollatzResearch.WordTrace tailWord_402675 prefixEnd_402675 137843881699544843940425 := by
  unfold tailWord_402675
  simp only [CollatzResearch.WordTrace]
  refine ⟨14686763816184721259937479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9791175877456480839958319 14686763816184721259937479)
  ·
    refine ⟨22030145724277081889906219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14686763816184721259937479 22030145724277081889906219)
    ·
      refine ⟨33045218586415622834859329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22030145724277081889906219 33045218586415622834859329)
      ·
        refine ⟨24783913939811717126144497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33045218586415622834859329 24783913939811717126144497)
        ·
          refine ⟨18587935454858787844608373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24783913939811717126144497 18587935454858787844608373)
          ·
            refine ⟨1742618948893011360432035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18587935454858787844608373 1742618948893011360432035)
            ·
              refine ⟨2613928423339517040648053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1742618948893011360432035 2613928423339517040648053)
              ·
                refine ⟨245055789688079722560755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2613928423339517040648053 245055789688079722560755)
                ·
                  refine ⟨367583684532119583841133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 245055789688079722560755 367583684532119583841133)
                  ·
                    refine ⟨137843881699544843940425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 367583684532119583841133 137843881699544843940425)
                    ·
                      rfl

theorem cell22_402675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5, 1, 3].length) (baseStart_402675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402675 prefixEnd_402675 := by exact prefixLift 402675
  have htrace : WordTrace (prefixWord ++ tailWord_402675) baseStart_402675 baseEnd_402675 := by
    simpa [prefixWord, tailWord_402675, baseEnd_402675] using wordTrace_append hprefix tailTrace_402675
  have hstable : (prefixWord ++ tailWord_402675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402675).length < 2 ^ (prefixWord ++ tailWord_402675).sum := by decide
  have hdescent : baseEnd_402675 < baseStart_402675 := by decide
  rcases family_descends (prefixWord ++ tailWord_402675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402692 : List Nat := [2, 3, 2, 2, 2, 1, 2, 4, 1, 3]
def baseStart_402692 : Nat := 118140960795 + 402692 * 2 ^ 59
def prefixEnd_402692 : Nat := 4983230072969 + 3 ^ 40 * 402692 * 2
def baseEnd_402692 : Nat := 137849701146962466265373

theorem tailTrace_402692 : CollatzResearch.WordTrace tailWord_402692 prefixEnd_402692 137849701146962466265373 := by
  unfold tailWord_402692
  simp only [CollatzResearch.WordTrace]
  refine ⟨7343691928561566581653165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9791589238082088775537553 7343691928561566581653165)
  ·
    refine ⟨2753884473210587468119937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7343691928561566581653165 2753884473210587468119937)
    ·
      refine ⟨2065413354907940601089953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2753884473210587468119937 2065413354907940601089953)
      ·
        refine ⟨1549060016180955450817465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2065413354907940601089953 1549060016180955450817465)
        ·
          refine ⟨1161795012135716588113099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1549060016180955450817465 1161795012135716588113099)
          ·
            refine ⟨1742692518203574882169649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1161795012135716588113099 1742692518203574882169649)
            ·
              refine ⟨1307019388652681161627237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1742692518203574882169649 1307019388652681161627237)
              ·
                refine ⟨245066135372377717805107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1307019388652681161627237 245066135372377717805107)
                ·
                  refine ⟨367599203058566576707661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 245066135372377717805107 367599203058566576707661)
                  ·
                    refine ⟨137849701146962466265373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 367599203058566576707661 137849701146962466265373)
                    ·
                      rfl

theorem cell22_402692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_402692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402692 prefixEnd_402692 := by exact prefixLift 402692
  have htrace : WordTrace (prefixWord ++ tailWord_402692) baseStart_402692 baseEnd_402692 := by
    simpa [prefixWord, tailWord_402692, baseEnd_402692] using wordTrace_append hprefix tailTrace_402692
  have hstable : (prefixWord ++ tailWord_402692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402692).length < 2 ^ (prefixWord ++ tailWord_402692).sum := by decide
  have hdescent : baseEnd_402692 < baseStart_402692 := by decide
  rcases family_descends (prefixWord ++ tailWord_402692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402761 : List Nat := [1, 2, 1, 1, 2, 3, 3, 9]
def baseStart_402761 : Nat := 118140960795 + 402761 * 2 ^ 59
def prefixEnd_402761 : Nat := 4983230072969 + 3 ^ 40 * 402761 * 2
def baseEnd_402761 : Nat := 15319257917452142921129

theorem tailTrace_402761 : CollatzResearch.WordTrace tailWord_402761 prefixEnd_402761 15319257917452142921129 := by
  unfold tailWord_402761
  simp only [CollatzResearch.WordTrace]
  refine ⟨14689900493873157947568137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9793266995915438631712091 14689900493873157947568137)
  ·
    refine ⟨11017425370404868460676103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14689900493873157947568137 11017425370404868460676103)
    ·
      refine ⟨16526138055607302691014155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11017425370404868460676103 16526138055607302691014155)
      ·
        refine ⟨24789207083410954036521233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16526138055607302691014155 24789207083410954036521233)
        ·
          refine ⟨18591905312558215527390925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24789207083410954036521233 18591905312558215527390925)
          ·
            refine ⟨6971964492209330822771597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18591905312558215527390925 6971964492209330822771597)
            ·
              refine ⟨2614486684578499058539349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6971964492209330822771597 2614486684578499058539349)
              ·
                refine ⟨15319257917452142921129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2614486684578499058539349 15319257917452142921129)
                ·
                  rfl

theorem cell22_402761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 9].length) (baseStart_402761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402761 prefixEnd_402761 := by exact prefixLift 402761
  have htrace : WordTrace (prefixWord ++ tailWord_402761) baseStart_402761 baseEnd_402761 := by
    simpa [prefixWord, tailWord_402761, baseEnd_402761] using wordTrace_append hprefix tailTrace_402761
  have hstable : (prefixWord ++ tailWord_402761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402761).length < 2 ^ (prefixWord ++ tailWord_402761).sum := by decide
  have hdescent : baseEnd_402761 < baseStart_402761 := by decide
  rcases family_descends (prefixWord ++ tailWord_402761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402793 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 7, 3]
def baseStart_402793 : Nat := 118140960795 + 402793 * 2 ^ 59
def prefixEnd_402793 : Nat := 4983230072969 + 3 ^ 40 * 402793 * 2
def baseEnd_402793 : Nat := 137884275511031869490063

theorem tailTrace_402793 : CollatzResearch.WordTrace tailWord_402793 prefixEnd_402793 137884275511031869490063 := by
  unfold tailWord_402793
  simp only [CollatzResearch.WordTrace]
  refine ⟨14691067629757227412733033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9794045086504818275155355 14691067629757227412733033)
  ·
    refine ⟨11018300722317920559549775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14691067629757227412733033 11018300722317920559549775)
    ·
      refine ⟨16527451083476880839324663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11018300722317920559549775 16527451083476880839324663)
      ·
        refine ⟨24791176625215321258986995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16527451083476880839324663 24791176625215321258986995)
        ·
          refine ⟨37186764937822981888480493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24791176625215321258986995 37186764937822981888480493)
          ·
            refine ⟨13945036851683618208180185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37186764937822981888480493 13945036851683618208180185)
            ·
              refine ⟨10458777638762713656135139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13945036851683618208180185 10458777638762713656135139)
              ·
                refine ⟨15688166458144070484202709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10458777638762713656135139 15688166458144070484202709)
                ·
                  refine ⟨367691401362751651973501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15688166458144070484202709 367691401362751651973501)
                  ·
                    refine ⟨137884275511031869490063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 367691401362751651973501 137884275511031869490063)
                    ·
                      rfl

theorem cell22_402793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7, 3].length) (baseStart_402793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402793 prefixEnd_402793 := by exact prefixLift 402793
  have htrace : WordTrace (prefixWord ++ tailWord_402793) baseStart_402793 baseEnd_402793 := by
    simpa [prefixWord, tailWord_402793, baseEnd_402793] using wordTrace_append hprefix tailTrace_402793
  have hstable : (prefixWord ++ tailWord_402793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402793).length < 2 ^ (prefixWord ++ tailWord_402793).sum := by decide
  have hdescent : baseEnd_402793 < baseStart_402793 := by decide
  rcases family_descends (prefixWord ++ tailWord_402793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402853 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 5, 4]
def baseStart_402853 : Nat := 118140960795 + 402853 * 2 ^ 59
def prefixEnd_402853 : Nat := 4983230072969 + 3 ^ 40 * 402853 * 2
def baseEnd_402853 : Nat := 137904814737211712989879

theorem tailTrace_402853 : CollatzResearch.WordTrace tailWord_402853 prefixEnd_402853 137904814737211712989879 := by
  unfold tailWord_402853
  simp only [CollatzResearch.WordTrace]
  refine ⟨14693256009539857659917213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9795504006359905106611475 14693256009539857659917213)
  ·
    refine ⟨5509971003577446622468955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14693256009539857659917213 5509971003577446622468955)
    ·
      refine ⟨8264956505366169933703433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5509971003577446622468955 8264956505366169933703433)
      ·
        refine ⟨6198717379024627450277575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8264956505366169933703433 6198717379024627450277575)
        ·
          refine ⟨9298076068536941175416363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6198717379024627450277575 9298076068536941175416363)
          ·
            refine ⟨13947114102805411763124545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9298076068536941175416363 13947114102805411763124545)
            ·
              refine ⟨10460335577104058822343409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13947114102805411763124545 10460335577104058822343409)
              ·
                refine ⟨7845251682828044116757557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10460335577104058822343409 7845251682828044116757557)
                ·
                  refine ⟨735492345265129135946021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7845251682828044116757557 735492345265129135946021)
                  ·
                    refine ⟨137904814737211712989879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 735492345265129135946021 137904814737211712989879)
                    ·
                      rfl

theorem cell22_402853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_402853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402853 prefixEnd_402853 := by exact prefixLift 402853
  have htrace : WordTrace (prefixWord ++ tailWord_402853) baseStart_402853 baseEnd_402853 := by
    simpa [prefixWord, tailWord_402853, baseEnd_402853] using wordTrace_append hprefix tailTrace_402853
  have hstable : (prefixWord ++ tailWord_402853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402853).length < 2 ^ (prefixWord ++ tailWord_402853).sum := by decide
  have hdescent : baseEnd_402853 < baseStart_402853 := by decide
  rcases family_descends (prefixWord ++ tailWord_402853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402913 : List Nat := [1, 2, 3, 1, 2, 3, 10]
def baseStart_402913 : Nat := 118140960795 + 402913 * 2 ^ 59
def prefixEnd_402913 : Nat := 4983230072969 + 3 ^ 40 * 402913 * 2
def baseEnd_402913 : Nat := 5108346443088576166285

theorem tailTrace_402913 : CollatzResearch.WordTrace tailWord_402913 prefixEnd_402913 5108346443088576166285 := by
  unfold tailWord_402913
  simp only [CollatzResearch.WordTrace]
  refine ⟨14695444389322487907101393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9796962926214991938067595 14695444389322487907101393)
  ·
    refine ⟨11021583291991865930326045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14695444389322487907101393 11021583291991865930326045)
    ·
      refine ⟨4133093734496949723872267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11021583291991865930326045 4133093734496949723872267)
      ·
        refine ⟨6199640601745424585808401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4133093734496949723872267 6199640601745424585808401)
        ·
          refine ⟨4649730451309068439356301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6199640601745424585808401 4649730451309068439356301)
          ·
            refine ⟨1743648919240900664758613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4649730451309068439356301 1743648919240900664758613)
            ·
              refine ⟨5108346443088576166285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1743648919240900664758613 5108346443088576166285)
              ·
                rfl

theorem cell22_402913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 10].length) (baseStart_402913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402913 prefixEnd_402913 := by exact prefixLift 402913
  have htrace : WordTrace (prefixWord ++ tailWord_402913) baseStart_402913 baseEnd_402913 := by
    simpa [prefixWord, tailWord_402913, baseEnd_402913] using wordTrace_append hprefix tailTrace_402913
  have hstable : (prefixWord ++ tailWord_402913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402913).length < 2 ^ (prefixWord ++ tailWord_402913).sum := by decide
  have hdescent : baseEnd_402913 < baseStart_402913 := by decide
  rcases family_descends (prefixWord ++ tailWord_402913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402915 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 4, 4]
def baseStart_402915 : Nat := 118140960795 + 402915 * 2 ^ 59
def prefixEnd_402915 : Nat := 4983230072969 + 3 ^ 40 * 402915 * 2
def baseEnd_402915 : Nat := 137926038604264217939689

theorem tailTrace_402915 : CollatzResearch.WordTrace tailWord_402915 prefixEnd_402915 137926038604264217939689 := by
  unfold tailWord_402915
  simp only [CollatzResearch.WordTrace]
  refine ⟨14695517335315242248674199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9797011556876828165782799 14695517335315242248674199)
  ·
    refine ⟨22043276002972863373011299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14695517335315242248674199 22043276002972863373011299)
    ·
      refine ⟨33064914004459295059516949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22043276002972863373011299 33064914004459295059516949)
      ·
        refine ⟨1549917843959029455914857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33064914004459295059516949 1549917843959029455914857)
        ·
          refine ⟨1162438382969272091936143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1549917843959029455914857 1162438382969272091936143)
          ·
            refine ⟨1743657574453908137904215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162438382969272091936143 1743657574453908137904215)
            ·
              refine ⟨2615486361680862206856323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1743657574453908137904215 2615486361680862206856323)
              ·
                refine ⟨3923229542521293310284485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2615486361680862206856323 3923229542521293310284485)
                ·
                  refine ⟨735605539222742495678341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3923229542521293310284485 735605539222742495678341)
                  ·
                    refine ⟨137926038604264217939689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 735605539222742495678341 137926038604264217939689)
                    ·
                      rfl

theorem cell22_402915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 4].length) (baseStart_402915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402915 prefixEnd_402915 := by exact prefixLift 402915
  have htrace : WordTrace (prefixWord ++ tailWord_402915) baseStart_402915 baseEnd_402915 := by
    simpa [prefixWord, tailWord_402915, baseEnd_402915] using wordTrace_append hprefix tailTrace_402915
  have hstable : (prefixWord ++ tailWord_402915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402915).length < 2 ^ (prefixWord ++ tailWord_402915).sum := by decide
  have hdescent : baseEnd_402915 < baseStart_402915 := by decide
  rcases family_descends (prefixWord ++ tailWord_402915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402917 : List Nat := [1, 3, 1, 5, 1, 1, 2, 1, 4, 3]
def baseStart_402917 : Nat := 118140960795 + 402917 * 2 ^ 59
def prefixEnd_402917 : Nat := 4983230072969 + 3 ^ 40 * 402917 * 2
def baseEnd_402917 : Nat := 137926723245136879389683

theorem tailTrace_402917 : CollatzResearch.WordTrace tailWord_402917 prefixEnd_402917 137926723245136879389683 := by
  unfold tailWord_402917
  simp only [CollatzResearch.WordTrace]
  refine ⟨14695590281307996590247005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9797060187538664393498003 14695590281307996590247005)
  ·
    refine ⟨5510846355490498721342627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14695590281307996590247005 5510846355490498721342627)
    ·
      refine ⟨8266269533235748082013941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5510846355490498721342627 8266269533235748082013941)
      ·
        refine ⟨774962768740851382688807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8266269533235748082013941 774962768740851382688807)
        ·
          refine ⟨1162444153111277074033211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 774962768740851382688807 1162444153111277074033211)
          ·
            refine ⟨1743666229666915611049817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162444153111277074033211 1743666229666915611049817)
            ·
              refine ⟨1307749672250186708287363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1743666229666915611049817 1307749672250186708287363)
              ·
                refine ⟨1961624508375280062431045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1307749672250186708287363 1961624508375280062431045)
                ·
                  refine ⟨367804595320365011705821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1961624508375280062431045 367804595320365011705821)
                  ·
                    refine ⟨137926723245136879389683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 367804595320365011705821 137926723245136879389683)
                    ·
                      rfl

theorem cell22_402917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4, 3].length) (baseStart_402917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402917 prefixEnd_402917 := by exact prefixLift 402917
  have htrace : WordTrace (prefixWord ++ tailWord_402917) baseStart_402917 baseEnd_402917 := by
    simpa [prefixWord, tailWord_402917, baseEnd_402917] using wordTrace_append hprefix tailTrace_402917
  have hstable : (prefixWord ++ tailWord_402917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402917).length < 2 ^ (prefixWord ++ tailWord_402917).sum := by decide
  have hdescent : baseEnd_402917 < baseStart_402917 := by decide
  rcases family_descends (prefixWord ++ tailWord_402917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402919 : List Nat := [1, 1, 5, 2, 1, 3, 3, 2, 4]
def baseStart_402919 : Nat := 118140960795 + 402919 * 2 ^ 59
def prefixEnd_402919 : Nat := 4983230072969 + 3 ^ 40 * 402919 * 2
def baseEnd_402919 : Nat := 45975802628669846946559

theorem tailTrace_402919 : CollatzResearch.WordTrace tailWord_402919 prefixEnd_402919 45975802628669846946559 := by
  unfold tailWord_402919
  simp only [CollatzResearch.WordTrace]
  refine ⟨14695663227300750931819811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9797108818200500621213207 14695663227300750931819811)
  ·
    refine ⟨22043494840951126397729717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14695663227300750931819811 22043494840951126397729717)
    ·
      refine ⟨2066577641339168099787161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22043494840951126397729717 2066577641339168099787161)
      ·
        refine ⟨1549933231004376074840371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2066577641339168099787161 1549933231004376074840371)
        ·
          refine ⟨2324899846506564112260557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1549933231004376074840371 2324899846506564112260557)
          ·
            refine ⟨871837442439961542097709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2324899846506564112260557 871837442439961542097709)
            ·
              refine ⟨326939040914985578286641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 871837442439961542097709 326939040914985578286641)
              ·
                refine ⟨245204280686239183714981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326939040914985578286641 245204280686239183714981)
                ·
                  refine ⟨45975802628669846946559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 245204280686239183714981 45975802628669846946559)
                  ·
                    rfl

theorem cell22_402919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2, 4].length) (baseStart_402919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402919 prefixEnd_402919 := by exact prefixLift 402919
  have htrace : WordTrace (prefixWord ++ tailWord_402919) baseStart_402919 baseEnd_402919 := by
    simpa [prefixWord, tailWord_402919, baseEnd_402919] using wordTrace_append hprefix tailTrace_402919
  have hstable : (prefixWord ++ tailWord_402919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402919).length < 2 ^ (prefixWord ++ tailWord_402919).sum := by decide
  have hdescent : baseEnd_402919 < baseStart_402919 := by decide
  rcases family_descends (prefixWord ++ tailWord_402919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402930 : List Nat := [3, 2, 1, 4, 1, 1, 1, 9]
def baseStart_402930 : Nat := 118140960795 + 402930 * 2 ^ 59
def prefixEnd_402930 : Nat := 4983230072969 + 3 ^ 40 * 402930 * 2
def baseEnd_402930 : Nat := 15325685934534353201627

theorem tailTrace_402930 : CollatzResearch.WordTrace tailWord_402930 prefixEnd_402930 15325685934534353201627 := by
  unfold tailWord_402930
  simp only [CollatzResearch.WordTrace]
  refine ⟨3674016107565224952617561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9797376286840599873646829 3674016107565224952617561)
  ·
    refine ⟨2755512080673918714463171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3674016107565224952617561 2755512080673918714463171)
    ·
      refine ⟨4133268121010878071694757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2755512080673918714463171 4133268121010878071694757)
      ·
        refine ⟨774987772689539638442767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4133268121010878071694757 774987772689539638442767)
        ·
          refine ⟨1162481659034309457664151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 774987772689539638442767 1162481659034309457664151)
          ·
            refine ⟨1743722488551464186496227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162481659034309457664151 1743722488551464186496227)
            ·
              refine ⟨2615583732827196279744341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1743722488551464186496227 2615583732827196279744341)
              ·
                refine ⟨15325685934534353201627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2615583732827196279744341 15325685934534353201627)
                ·
                  rfl

theorem cell22_402930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 9].length) (baseStart_402930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402930 prefixEnd_402930 := by exact prefixLift 402930
  have htrace : WordTrace (prefixWord ++ tailWord_402930) baseStart_402930 baseEnd_402930 := by
    simpa [prefixWord, tailWord_402930, baseEnd_402930] using wordTrace_append hprefix tailTrace_402930
  have hstable : (prefixWord ++ tailWord_402930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402930).length < 2 ^ (prefixWord ++ tailWord_402930).sum := by decide
  have hdescent : baseEnd_402930 < baseStart_402930 := by decide
  rcases family_descends (prefixWord ++ tailWord_402930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402934 : List Nat := [5, 1, 1, 1, 2, 3, 1, 3, 2, 3]
def baseStart_402934 : Nat := 118140960795 + 402934 * 2 ^ 59
def prefixEnd_402934 : Nat := 4983230072969 + 3 ^ 40 * 402934 * 2
def baseEnd_402934 : Nat := 137932542692554501714631

theorem tailTrace_402934 : CollatzResearch.WordTrace tailWord_402934 prefixEnd_402934 137932542692554501714631 := by
  unfold tailWord_402934
  simp only [CollatzResearch.WordTrace]
  refine ⟨918513145140400530850991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9797473548164272329077237 918513145140400530850991)
  ·
    refine ⟨1377769717710600796276487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 918513145140400530850991 1377769717710600796276487)
    ·
      refine ⟨2066654576565901194414731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1377769717710600796276487 2066654576565901194414731)
      ·
        refine ⟨3099981864848851791622097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2066654576565901194414731 3099981864848851791622097)
        ·
          refine ⟨2324986398636638843716573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3099981864848851791622097 2324986398636638843716573)
          ·
            refine ⟨871869899488739566393715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2324986398636638843716573 871869899488739566393715)
            ·
              refine ⟨1307804849233109349590573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 871869899488739566393715 1307804849233109349590573)
              ·
                refine ⟨490426818462416006096465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1307804849233109349590573 490426818462416006096465)
                ·
                  refine ⟨367820113846812004572349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 490426818462416006096465 367820113846812004572349)
                  ·
                    refine ⟨137932542692554501714631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 367820113846812004572349 137932542692554501714631)
                    ·
                      rfl

theorem cell22_402934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_402934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402934 prefixEnd_402934 := by exact prefixLift 402934
  have htrace : WordTrace (prefixWord ++ tailWord_402934) baseStart_402934 baseEnd_402934 := by
    simpa [prefixWord, tailWord_402934, baseEnd_402934] using wordTrace_append hprefix tailTrace_402934
  have hstable : (prefixWord ++ tailWord_402934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402934).length < 2 ^ (prefixWord ++ tailWord_402934).sum := by decide
  have hdescent : baseEnd_402934 < baseStart_402934 := by decide
  rcases family_descends (prefixWord ++ tailWord_402934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402943 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 4, 6]
def baseStart_402943 : Nat := 118140960795 + 402943 * 2 ^ 59
def prefixEnd_402943 : Nat := 4983230072969 + 3 ^ 40 * 402943 * 2
def baseEnd_402943 : Nat := 137935623576481478239603

theorem tailTrace_402943 : CollatzResearch.WordTrace tailWord_402943 prefixEnd_402943 137935623576481478239603 := by
  unfold tailWord_402943
  simp only [CollatzResearch.WordTrace]
  refine ⟨14696538579213803030693483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9797692386142535353795655 14696538579213803030693483)
  ·
    refine ⟨22044807868820704546040225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14696538579213803030693483 22044807868820704546040225)
    ·
      refine ⟨16533605901615528409530169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22044807868820704546040225 16533605901615528409530169)
      ·
        refine ⟨12400204426211646307147627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16533605901615528409530169 12400204426211646307147627)
        ·
          refine ⟨18600306639317469460721441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12400204426211646307147627 18600306639317469460721441)
          ·
            refine ⟨13950229979488102095541081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18600306639317469460721441 13950229979488102095541081)
            ·
              refine ⟨10462672484616076571655811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13950229979488102095541081 10462672484616076571655811)
              ·
                refine ⟨15694008726924114857483717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10462672484616076571655811 15694008726924114857483717)
                ·
                  refine ⟨2942626636298271535778197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15694008726924114857483717 2942626636298271535778197)
                  ·
                    refine ⟨137935623576481478239603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2942626636298271535778197 137935623576481478239603)
                    ·
                      rfl

theorem cell22_402943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 6].length) (baseStart_402943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402943 prefixEnd_402943 := by exact prefixLift 402943
  have htrace : WordTrace (prefixWord ++ tailWord_402943) baseStart_402943 baseEnd_402943 := by
    simpa [prefixWord, tailWord_402943, baseEnd_402943] using wordTrace_append hprefix tailTrace_402943
  have hstable : (prefixWord ++ tailWord_402943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402943).length < 2 ^ (prefixWord ++ tailWord_402943).sum := by decide
  have hdescent : baseEnd_402943 < baseStart_402943 := by decide
  rcases family_descends (prefixWord ++ tailWord_402943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402975 : List Nat := [1, 1, 2, 4, 1, 1, 3, 4, 5]
def baseStart_402975 : Nat := 118140960795 + 402975 * 2 ^ 59
def prefixEnd_402975 : Nat := 4983230072969 + 3 ^ 40 * 402975 * 2
def baseEnd_402975 : Nat := 45982192610148020479835

theorem tailTrace_402975 : CollatzResearch.WordTrace tailWord_402975 prefixEnd_402975 45982192610148020479835 := by
  unfold tailWord_402975
  simp only [CollatzResearch.WordTrace]
  refine ⟨14697705715097872495858379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9798470476731914997238919 14697705715097872495858379)
  ·
    refine ⟨22046558572646808743787569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14697705715097872495858379 22046558572646808743787569)
    ·
      refine ⟨16534918929485106557840677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22046558572646808743787569 16534918929485106557840677)
      ·
        refine ⟨3100297299278457479595127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16534918929485106557840677 3100297299278457479595127)
        ·
          refine ⟨4650445948917686219392691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3100297299278457479595127 4650445948917686219392691)
          ·
            refine ⟨6975668923376529329089037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4650445948917686219392691 6975668923376529329089037)
            ·
              refine ⟨2615875846266198498408389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6975668923376529329089037 2615875846266198498408389)
              ·
                refine ⟨490476721174912218451573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2615875846266198498408389 490476721174912218451573)
                ·
                  refine ⟨45982192610148020479835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 490476721174912218451573 45982192610148020479835)
                  ·
                    rfl

theorem cell22_402975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 5].length) (baseStart_402975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_402975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_402975 prefixEnd_402975 := by exact prefixLift 402975
  have htrace : WordTrace (prefixWord ++ tailWord_402975) baseStart_402975 baseEnd_402975 := by
    simpa [prefixWord, tailWord_402975, baseEnd_402975] using wordTrace_append hprefix tailTrace_402975
  have hstable : (prefixWord ++ tailWord_402975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402975).length < 2 ^ (prefixWord ++ tailWord_402975).sum := by decide
  have hdescent : baseEnd_402975 < baseStart_402975 := by decide
  rcases family_descends (prefixWord ++ tailWord_402975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403065 : List Nat := [1, 2, 1, 3, 3, 1, 3, 8]
def baseStart_403065 : Nat := 118140960795 + 403065 * 2 ^ 59
def prefixEnd_403065 : Nat := 4983230072969 + 3 ^ 40 * 403065 * 2
def baseEnd_403065 : Nat := 15330820741079314076581

theorem tailTrace_403065 : CollatzResearch.WordTrace tailWord_403065 prefixEnd_403065 15330820741079314076581 := by
  unfold tailWord_403065
  simp only [CollatzResearch.WordTrace]
  refine ⟨14700988284771817866634649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9800658856514545244423099 14700988284771817866634649)
  ·
    refine ⟨11025741213578863399975987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14700988284771817866634649 11025741213578863399975987)
    ·
      refine ⟨16538611820368295099963981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11025741213578863399975987 16538611820368295099963981)
      ·
        refine ⟨6201979432638110662486493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16538611820368295099963981 6201979432638110662486493)
        ·
          refine ⟨2325742287239291498432435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6201979432638110662486493 2325742287239291498432435)
          ·
            refine ⟨3488613430858937247648653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2325742287239291498432435 3488613430858937247648653)
            ·
              refine ⟨1308230036572101467868245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3488613430858937247648653 1308230036572101467868245)
              ·
                refine ⟨15330820741079314076581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1308230036572101467868245 15330820741079314076581)
                ·
                  rfl

theorem cell22_403065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 8].length) (baseStart_403065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403065 prefixEnd_403065 := by exact prefixLift 403065
  have htrace : WordTrace (prefixWord ++ tailWord_403065) baseStart_403065 baseEnd_403065 := by
    simpa [prefixWord, tailWord_403065, baseEnd_403065] using wordTrace_append hprefix tailTrace_403065
  have hstable : (prefixWord ++ tailWord_403065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403065).length < 2 ^ (prefixWord ++ tailWord_403065).sum := by decide
  have hdescent : baseEnd_403065 < baseStart_403065 := by decide
  rcases family_descends (prefixWord ++ tailWord_403065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403082 : List Nat := [3, 1, 2, 3, 2, 3, 8]
def baseStart_403082 : Nat := 118140960795 + 403082 * 2 ^ 59
def prefixEnd_403082 : Nat := 4983230072969 + 3 ^ 40 * 403082 * 2
def baseEnd_403082 : Nat := 5110489115449312926451

theorem tailTrace_403082 : CollatzResearch.WordTrace tailWord_403082 prefixEnd_403082 5110489115449312926451 := by
  unfold tailWord_403082
  simp only [CollatzResearch.WordTrace]
  refine ⟨3675402081427557442500875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9801072217140153180002333 3675402081427557442500875)
  ·
    refine ⟨5513103122141336163751313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3675402081427557442500875 5513103122141336163751313)
    ·
      refine ⟨4134827341606002122813485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5513103122141336163751313 4134827341606002122813485)
      ·
        refine ⟨1550560253102250796055057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4134827341606002122813485 1550560253102250796055057)
        ·
          refine ⟨1162920189826688097041293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1550560253102250796055057 1162920189826688097041293)
          ·
            refine ⟨436095071185008036390485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1162920189826688097041293 436095071185008036390485)
            ·
              refine ⟨5110489115449312926451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 436095071185008036390485 5110489115449312926451)
              ·
                rfl

theorem cell22_403082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 8].length) (baseStart_403082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403082 prefixEnd_403082 := by exact prefixLift 403082
  have htrace : WordTrace (prefixWord ++ tailWord_403082) baseStart_403082 baseEnd_403082 := by
    simpa [prefixWord, tailWord_403082, baseEnd_403082] using wordTrace_append hprefix tailTrace_403082
  have hstable : (prefixWord ++ tailWord_403082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403082).length < 2 ^ (prefixWord ++ tailWord_403082).sum := by decide
  have hdescent : baseEnd_403082 < baseStart_403082 := by decide
  rcases family_descends (prefixWord ++ tailWord_403082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403097 : List Nat := [1, 2, 1, 2, 1, 2, 2, 5, 3, 3]
def baseStart_403097 : Nat := 118140960795 + 403097 * 2 ^ 59
def prefixEnd_403097 : Nat := 4983230072969 + 3 ^ 40 * 403097 * 2
def baseEnd_403097 : Nat := 137988340923676409889131

theorem tailTrace_403097 : CollatzResearch.WordTrace tailWord_403097 prefixEnd_403097 137988340923676409889131 := by
  unfold tailWord_403097
  simp only [CollatzResearch.WordTrace]
  refine ⟨14702155420655887331799545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9801436947103924887866363 14702155420655887331799545)
  ·
    refine ⟨11026616565491915498849659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14702155420655887331799545 11026616565491915498849659)
    ·
      refine ⟨16539924848237873248274489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11026616565491915498849659 16539924848237873248274489)
      ·
        refine ⟨12404943636178404936205867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16539924848237873248274489 12404943636178404936205867)
        ·
          refine ⟨18607415454267607404308801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12404943636178404936205867 18607415454267607404308801)
          ·
            refine ⟨13955561590700705553231601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18607415454267607404308801 13955561590700705553231601)
            ·
              refine ⟨10466671193025529164923701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13955561590700705553231601 10466671193025529164923701)
              ·
                refine ⟨981250424346143359211597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10466671193025529164923701 981250424346143359211597)
                ·
                  refine ⟨367968909129803759704349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 981250424346143359211597 367968909129803759704349)
                  ·
                    refine ⟨137988340923676409889131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 367968909129803759704349 137988340923676409889131)
                    ·
                      rfl

theorem cell22_403097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3, 3].length) (baseStart_403097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403097 prefixEnd_403097 := by exact prefixLift 403097
  have htrace : WordTrace (prefixWord ++ tailWord_403097) baseStart_403097 baseEnd_403097 := by
    simpa [prefixWord, tailWord_403097, baseEnd_403097] using wordTrace_append hprefix tailTrace_403097
  have hstable : (prefixWord ++ tailWord_403097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403097).length < 2 ^ (prefixWord ++ tailWord_403097).sum := by decide
  have hdescent : baseEnd_403097 < baseStart_403097 := by decide
  rcases family_descends (prefixWord ++ tailWord_403097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403148 : List Nat := [2, 2, 1, 5, 2, 1, 1, 4, 1, 3]
def baseStart_403148 : Nat := 118140960795 + 403148 * 2 ^ 59
def prefixEnd_403148 : Nat := 4983230072969 + 3 ^ 40 * 403148 * 2
def baseEnd_403148 : Nat := 138005799265929276863975

theorem tailTrace_403148 : CollatzResearch.WordTrace tailWord_403148 prefixEnd_403148 138005799265929276863975 := by
  unfold tailWord_403148
  simp only [CollatzResearch.WordTrace]
  refine ⟨7352007771735561520953049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9802677028980748694604065 7352007771735561520953049)
  ·
    refine ⟨5514005828801671140714787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7352007771735561520953049 5514005828801671140714787)
    ·
      refine ⟨8271008743202506711072181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5514005828801671140714787 8271008743202506711072181)
      ·
        refine ⟨775407069675235004163017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8271008743202506711072181 775407069675235004163017)
        ·
          refine ⟨581555302256426253122263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 775407069675235004163017 581555302256426253122263)
          ·
            refine ⟨872332953384639379683395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581555302256426253122263 872332953384639379683395)
            ·
              refine ⟨1308499430076959069525093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 872332953384639379683395 1308499430076959069525093)
              ·
                refine ⟨245343643139429825535955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1308499430076959069525093 245343643139429825535955)
                ·
                  refine ⟨368015464709144738303933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 245343643139429825535955 368015464709144738303933)
                  ·
                    refine ⟨138005799265929276863975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 368015464709144738303933 138005799265929276863975)
                    ·
                      rfl

theorem cell22_403148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4, 1, 3].length) (baseStart_403148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403148 prefixEnd_403148 := by exact prefixLift 403148
  have htrace : WordTrace (prefixWord ++ tailWord_403148) baseStart_403148 baseEnd_403148 := by
    simpa [prefixWord, tailWord_403148, baseEnd_403148] using wordTrace_append hprefix tailTrace_403148
  have hstable : (prefixWord ++ tailWord_403148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403148).length < 2 ^ (prefixWord ++ tailWord_403148).sum := by decide
  have hdescent : baseEnd_403148 < baseStart_403148 := by decide
  rcases family_descends (prefixWord ++ tailWord_403148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403172 : List Nat := [2, 3, 1, 1, 1, 3, 3, 2, 6]
def baseStart_403172 : Nat := 118140960795 + 403172 * 2 ^ 59
def prefixEnd_403172 : Nat := 4983230072969 + 3 ^ 40 * 403172 * 2
def baseEnd_403172 : Nat := 46004671652133738087967

theorem tailTrace_403172 : CollatzResearch.WordTrace tailWord_403172 prefixEnd_403172 46004671652133738087967 := by
  unfold tailWord_403172
  simp only [CollatzResearch.WordTrace]
  refine ⟨7352445447692087570389885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9803260596922783427186513 7352445447692087570389885)
  ·
    refine ⟨2757167042884532838896207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7352445447692087570389885 2757167042884532838896207)
    ·
      refine ⟨4135750564326799258344311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2757167042884532838896207 4135750564326799258344311)
      ·
        refine ⟨6203625846490198887516467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4135750564326799258344311 6203625846490198887516467)
        ·
          refine ⟨9305438769735298331274701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6203625846490198887516467 9305438769735298331274701)
          ·
            refine ⟨3489539538650736874228013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9305438769735298331274701 3489539538650736874228013)
            ·
              refine ⟨1308577326994026327835505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3489539538650736874228013 1308577326994026327835505)
              ·
                refine ⟨981432995245519745876629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1308577326994026327835505 981432995245519745876629)
                ·
                  refine ⟨46004671652133738087967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 981432995245519745876629 46004671652133738087967)
                  ·
                    rfl

theorem cell22_403172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_403172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403172 prefixEnd_403172 := by exact prefixLift 403172
  have htrace : WordTrace (prefixWord ++ tailWord_403172) baseStart_403172 baseEnd_403172 := by
    simpa [prefixWord, tailWord_403172, baseEnd_403172] using wordTrace_append hprefix tailTrace_403172
  have hstable : (prefixWord ++ tailWord_403172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403172).length < 2 ^ (prefixWord ++ tailWord_403172).sum := by decide
  have hdescent : baseEnd_403172 < baseStart_403172 := by decide
  rcases family_descends (prefixWord ++ tailWord_403172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403187 : List Nat := [1, 1, 1, 2, 2, 3, 4, 2, 1, 5]
def baseStart_403187 : Nat := 118140960795 + 403187 * 2 ^ 59
def prefixEnd_403187 : Nat := 4983230072969 + 3 ^ 40 * 403187 * 2
def baseEnd_403187 : Nat := 138019149762946175138855

theorem tailTrace_403187 : CollatzResearch.WordTrace tailWord_403187 prefixEnd_403187 138019149762946175138855 := by
  unfold tailWord_403187
  simp only [CollatzResearch.WordTrace]
  refine ⟨14705437990329832702575815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9803625326886555135050543 14705437990329832702575815)
  ·
    refine ⟨22058156985494749053863723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14705437990329832702575815 22058156985494749053863723)
    ·
      refine ⟨33087235478242123580795585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22058156985494749053863723 33087235478242123580795585)
      ·
        refine ⟨24815426608681592685596689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33087235478242123580795585 24815426608681592685596689)
        ·
          refine ⟨18611569956511194514197517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24815426608681592685596689 18611569956511194514197517)
          ·
            refine ⟨6979338733691697942824069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18611569956511194514197517 6979338733691697942824069)
            ·
              refine ⟨1308626012567193364279513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6979338733691697942824069 1308626012567193364279513)
              ·
                refine ⟨981469509425395023209635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1308626012567193364279513 981469509425395023209635)
                ·
                  refine ⟨1472204264138092534814453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 981469509425395023209635 1472204264138092534814453)
                  ·
                    refine ⟨138019149762946175138855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1472204264138092534814453 138019149762946175138855)
                    ·
                      rfl

theorem cell22_403187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 5].length) (baseStart_403187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403187 prefixEnd_403187 := by exact prefixLift 403187
  have htrace : WordTrace (prefixWord ++ tailWord_403187) baseStart_403187 baseEnd_403187 := by
    simpa [prefixWord, tailWord_403187, baseEnd_403187] using wordTrace_append hprefix tailTrace_403187
  have hstable : (prefixWord ++ tailWord_403187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403187).length < 2 ^ (prefixWord ++ tailWord_403187).sum := by decide
  have hdescent : baseEnd_403187 < baseStart_403187 := by decide
  rcases family_descends (prefixWord ++ tailWord_403187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403232 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 2, 7]
def baseStart_403232 : Nat := 118140960795 + 403232 * 2 ^ 59
def prefixEnd_403232 : Nat := 4983230072969 + 3 ^ 40 * 403232 * 2
def baseEnd_403232 : Nat := 138034554182581057763717

theorem tailTrace_403232 : CollatzResearch.WordTrace tailWord_403232 prefixEnd_403232 138034554182581057763717 := by
  unfold tailWord_403232
  simp only [CollatzResearch.WordTrace]
  refine ⟨7353539637583402693981975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9804719516777870258642633 7353539637583402693981975)
  ·
    refine ⟨11030309456375104040972963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7353539637583402693981975 11030309456375104040972963)
    ·
      refine ⟨16545464184562656061459445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11030309456375104040972963 16545464184562656061459445)
      ·
        refine ⟨1551137267302749005761823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16545464184562656061459445 1551137267302749005761823)
        ·
          refine ⟨2326705900954123508642735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1551137267302749005761823 2326705900954123508642735)
          ·
            refine ⟨3490058851431185262964103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2326705900954123508642735 3490058851431185262964103)
            ·
              refine ⟨5235088277146777894446155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3490058851431185262964103 5235088277146777894446155)
              ·
                refine ⟨7852632415720166841669233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5235088277146777894446155 7852632415720166841669233)
                ·
                  refine ⟨5889474311790125131251925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7852632415720166841669233 5889474311790125131251925)
                  ·
                    refine ⟨138034554182581057763717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5889474311790125131251925 138034554182581057763717)
                    ·
                      rfl

theorem cell22_403232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 2, 7].length) (baseStart_403232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403232 prefixEnd_403232 := by exact prefixLift 403232
  have htrace : WordTrace (prefixWord ++ tailWord_403232) baseStart_403232 baseEnd_403232 := by
    simpa [prefixWord, tailWord_403232, baseEnd_403232] using wordTrace_append hprefix tailTrace_403232
  have hstable : (prefixWord ++ tailWord_403232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403232).length < 2 ^ (prefixWord ++ tailWord_403232).sum := by decide
  have hdescent : baseEnd_403232 < baseStart_403232 := by decide
  rcases family_descends (prefixWord ++ tailWord_403232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403339 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 6, 3]
def baseStart_403339 : Nat := 118140960795 + 403339 * 2 ^ 59
def prefixEnd_403339 : Nat := 4983230072969 + 3 ^ 40 * 403339 * 2
def baseEnd_403339 : Nat := 138071182469268445338389

theorem tailTrace_403339 : CollatzResearch.WordTrace tailWord_403339 prefixEnd_403339 138071182469268445338389 := by
  unfold tailWord_403339
  simp only [CollatzResearch.WordTrace]
  refine ⟨14710981885779162662109071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9807321257186108441406047 14710981885779162662109071)
  ·
    refine ⟨22066472828668743993163607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14710981885779162662109071 22066472828668743993163607)
    ·
      refine ⟨33099709243003115989745411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22066472828668743993163607 33099709243003115989745411)
      ·
        refine ⟨49649563864504673984618117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33099709243003115989745411 49649563864504673984618117)
        ·
          refine ⟨9309293224594626372115897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49649563864504673984618117 9309293224594626372115897)
          ·
            refine ⟨6981969918445969779086923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9309293224594626372115897 6981969918445969779086923)
            ·
              refine ⟨10472954877668954668630385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6981969918445969779086923 10472954877668954668630385)
              ·
                refine ⟨7854716158251716001472789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10472954877668954668630385 7854716158251716001472789)
                ·
                  refine ⟨368189819918049187569037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7854716158251716001472789 368189819918049187569037)
                  ·
                    refine ⟨138071182469268445338389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 368189819918049187569037 138071182469268445338389)
                    ·
                      rfl

theorem cell22_403339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6, 3].length) (baseStart_403339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403339 prefixEnd_403339 := by exact prefixLift 403339
  have htrace : WordTrace (prefixWord ++ tailWord_403339) baseStart_403339 baseEnd_403339 := by
    simpa [prefixWord, tailWord_403339, baseEnd_403339] using wordTrace_append hprefix tailTrace_403339
  have hstable : (prefixWord ++ tailWord_403339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403339).length < 2 ^ (prefixWord ++ tailWord_403339).sum := by decide
  have hdescent : baseEnd_403339 < baseStart_403339 := by decide
  rcases family_descends (prefixWord ++ tailWord_403339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403356 : List Nat := [2, 2, 3, 3, 1, 1, 2, 2, 1, 5]
def baseStart_403356 : Nat := 118140960795 + 403356 * 2 ^ 59
def prefixEnd_403356 : Nat := 4983230072969 + 3 ^ 40 * 403356 * 2
def baseEnd_403356 : Nat := 138077001916686067663337

theorem tailTrace_403356 : CollatzResearch.WordTrace tailWord_403356 prefixEnd_403356 138077001916686067663337 := by
  unfold tailWord_403356
  simp only [CollatzResearch.WordTrace]
  refine ⟨7355800963358787282738961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9807734617811716376985281 7355800963358787282738961)
  ·
    refine ⟨5516850722519090462054221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7355800963358787282738961 5516850722519090462054221)
    ·
      refine ⟨2068819020944658923270333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5516850722519090462054221 2068819020944658923270333)
      ·
        refine ⟨775807132854247096226375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2068819020944658923270333 775807132854247096226375)
        ·
          refine ⟨1163710699281370644339563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775807132854247096226375 1163710699281370644339563)
          ·
            refine ⟨1745566048922055966509345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1163710699281370644339563 1745566048922055966509345)
            ·
              refine ⟨1309174536691541974882009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1745566048922055966509345 1309174536691541974882009)
              ·
                refine ⟨981880902518656481161507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1309174536691541974882009 981880902518656481161507)
                ·
                  refine ⟨1472821353777984721742261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 981880902518656481161507 1472821353777984721742261)
                  ·
                    refine ⟨138077001916686067663337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1472821353777984721742261 138077001916686067663337)
                    ·
                      rfl

theorem cell22_403356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_403356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403356 prefixEnd_403356 := by exact prefixLift 403356
  have htrace : WordTrace (prefixWord ++ tailWord_403356) baseStart_403356 baseEnd_403356 := by
    simpa [prefixWord, tailWord_403356, baseEnd_403356] using wordTrace_append hprefix tailTrace_403356
  have hstable : (prefixWord ++ tailWord_403356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403356).length < 2 ^ (prefixWord ++ tailWord_403356).sum := by decide
  have hdescent : baseEnd_403356 < baseStart_403356 := by decide
  rcases family_descends (prefixWord ++ tailWord_403356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403390 : List Nat := [4, 2, 1, 1, 1, 4, 3, 1, 2, 3]
def baseStart_403390 : Nat := 118140960795 + 403390 * 2 ^ 59
def prefixEnd_403390 : Nat := 4983230072969 + 3 ^ 40 * 403390 * 2
def baseEnd_403390 : Nat := 138088640811521312313233

theorem tailTrace_403390 : CollatzResearch.WordTrace tailWord_403390 prefixEnd_403390 138088640811521312313233 := by
  unfold tailWord_403390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1839105251074299796526953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9808561339062932248143749 1839105251074299796526953)
  ·
    refine ⟨1379328938305724847395215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1839105251074299796526953 1379328938305724847395215)
    ·
      refine ⟨2068993407458587271092823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1379328938305724847395215 2068993407458587271092823)
      ·
        refine ⟨3103490111187880906639235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2068993407458587271092823 3103490111187880906639235)
        ·
          refine ⟨4655235166781821359958853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3103490111187880906639235 4655235166781821359958853)
          ·
            refine ⟨872856593771591504992285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4655235166781821359958853 872856593771591504992285)
            ·
              refine ⟨327321222664346814372107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 872856593771591504992285 327321222664346814372107)
              ·
                refine ⟨490981833996520221558161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327321222664346814372107 490981833996520221558161)
                ·
                  refine ⟨368236375497390166168621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 490981833996520221558161 368236375497390166168621)
                  ·
                    refine ⟨138088640811521312313233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 368236375497390166168621 138088640811521312313233)
                    ·
                      rfl

theorem cell22_403390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_403390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403390 prefixEnd_403390 := by exact prefixLift 403390
  have htrace : WordTrace (prefixWord ++ tailWord_403390) baseStart_403390 baseEnd_403390 := by
    simpa [prefixWord, tailWord_403390, baseEnd_403390] using wordTrace_append hprefix tailTrace_403390
  have hstable : (prefixWord ++ tailWord_403390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403390).length < 2 ^ (prefixWord ++ tailWord_403390).sum := by decide
  have hdescent : baseEnd_403390 < baseStart_403390 := by decide
  rcases family_descends (prefixWord ++ tailWord_403390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403420 : List Nat := [2, 2, 6, 1, 1, 2, 8]
def baseStart_403420 : Nat := 118140960795 + 403420 * 2 ^ 59
def prefixEnd_403420 : Nat := 4983230072969 + 3 ^ 40 * 403420 * 2
def baseEnd_403420 : Nat := 5114774460170786446783

theorem tailTrace_403420 : CollatzResearch.WordTrace tailWord_403420 prefixEnd_403420 5114774460170786446783 := by
  unfold tailWord_403420
  simp only [CollatzResearch.WordTrace]
  refine ⟨7356968099242856747903857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9809290798990475663871809 7356968099242856747903857)
  ·
    refine ⟨5517726074432142560927893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7356968099242856747903857 5517726074432142560927893)
    ·
      refine ⟨258643409739006682543495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5517726074432142560927893 258643409739006682543495)
      ·
        refine ⟨387965114608510023815243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258643409739006682543495 387965114608510023815243)
        ·
          refine ⟨581947671912765035722865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387965114608510023815243 581947671912765035722865)
          ·
            refine ⟨436460753934573776792149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 581947671912765035722865 436460753934573776792149)
            ·
              refine ⟨5114774460170786446783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 436460753934573776792149 5114774460170786446783)
              ·
                rfl

theorem cell22_403420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 8].length) (baseStart_403420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403420 prefixEnd_403420 := by exact prefixLift 403420
  have htrace : WordTrace (prefixWord ++ tailWord_403420) baseStart_403420 baseEnd_403420 := by
    simpa [prefixWord, tailWord_403420, baseEnd_403420] using wordTrace_append hprefix tailTrace_403420
  have hstable : (prefixWord ++ tailWord_403420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403420).length < 2 ^ (prefixWord ++ tailWord_403420).sum := by decide
  have hdescent : baseEnd_403420 < baseStart_403420 := by decide
  rcases family_descends (prefixWord ++ tailWord_403420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403459 : List Nat := [1, 1, 1, 3, 2, 1, 1, 6, 6]
def baseStart_403459 : Nat := 118140960795 + 403459 * 2 ^ 59
def prefixEnd_403459 : Nat := 4983230072969 + 3 ^ 40 * 403459 * 2
def baseEnd_403459 : Nat := 46037420307209377446007

theorem tailTrace_403459 : CollatzResearch.WordTrace tailWord_403459 prefixEnd_403459 46037420307209377446007 := by
  unfold tailWord_403459
  simp only [CollatzResearch.WordTrace]
  refine ⟨14715358645344423156477431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9810239096896282104318287 14715358645344423156477431)
  ·
    refine ⟨22073037968016634734716147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14715358645344423156477431 22073037968016634734716147)
    ·
      refine ⟨33109556952024952102074221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22073037968016634734716147 33109556952024952102074221)
      ·
        refine ⟨12416083857009357038277833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33109556952024952102074221 12416083857009357038277833)
        ·
          refine ⟨9312062892757017778708375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12416083857009357038277833 9312062892757017778708375)
          ·
            refine ⟨13968094339135526668062563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9312062892757017778708375 13968094339135526668062563)
            ·
              refine ⟨20952141508703290002093845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13968094339135526668062563 20952141508703290002093845)
              ·
                refine ⟨982131633220466718848149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20952141508703290002093845 982131633220466718848149)
                ·
                  refine ⟨46037420307209377446007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 982131633220466718848149 46037420307209377446007)
                  ·
                    rfl

theorem cell22_403459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 6].length) (baseStart_403459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403459 prefixEnd_403459 := by exact prefixLift 403459
  have htrace : WordTrace (prefixWord ++ tailWord_403459) baseStart_403459 baseEnd_403459 := by
    simpa [prefixWord, tailWord_403459, baseEnd_403459] using wordTrace_append hprefix tailTrace_403459
  have hstable : (prefixWord ++ tailWord_403459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403459).length < 2 ^ (prefixWord ++ tailWord_403459).sum := by decide
  have hdescent : baseEnd_403459 < baseStart_403459 := by decide
  rcases family_descends (prefixWord ++ tailWord_403459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403461 : List Nat := [1, 3, 1, 1, 2, 5, 1, 1, 3, 4]
def baseStart_403461 : Nat := 118140960795 + 403461 * 2 ^ 59
def prefixEnd_403461 : Nat := 4983230072969 + 3 ^ 40 * 403461 * 2
def baseEnd_403461 : Nat := 138112945562500793788015

theorem tailTrace_403461 : CollatzResearch.WordTrace tailWord_403461 prefixEnd_403461 138112945562500793788015 := by
  unfold tailWord_403461
  simp only [CollatzResearch.WordTrace]
  refine ⟨14715431591337177498050237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9810287727558118332033491 14715431591337177498050237)
  ·
    refine ⟨5518286846751441561768839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14715431591337177498050237 5518286846751441561768839)
    ·
      refine ⟨8277430270127162342653259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5518286846751441561768839 8277430270127162342653259)
      ·
        refine ⟨12416145405190743513979889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8277430270127162342653259 12416145405190743513979889)
        ·
          refine ⟨9312109053893057635484917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12416145405190743513979889 9312109053893057635484917)
          ·
            refine ⟨873010223802474153326711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9312109053893057635484917 873010223802474153326711)
            ·
              refine ⟨1309515335703711229990067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 873010223802474153326711 1309515335703711229990067)
              ·
                refine ⟨1964273003555566844985101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1309515335703711229990067 1964273003555566844985101)
                ·
                  refine ⟨736602376333337566869413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1964273003555566844985101 736602376333337566869413)
                  ·
                    refine ⟨138112945562500793788015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 736602376333337566869413 138112945562500793788015)
                    ·
                      rfl

theorem cell22_403461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_403461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403461 prefixEnd_403461 := by exact prefixLift 403461
  have htrace : WordTrace (prefixWord ++ tailWord_403461) baseStart_403461 baseEnd_403461 := by
    simpa [prefixWord, tailWord_403461, baseEnd_403461] using wordTrace_append hprefix tailTrace_403461
  have hstable : (prefixWord ++ tailWord_403461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403461).length < 2 ^ (prefixWord ++ tailWord_403461).sum := by decide
  have hdescent : baseEnd_403461 < baseStart_403461 := by decide
  rcases family_descends (prefixWord ++ tailWord_403461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403493 : List Nat := [1, 3, 1, 2, 2, 4, 1, 4, 4]
def baseStart_403493 : Nat := 118140960795 + 403493 * 2 ^ 59
def prefixEnd_403493 : Nat := 4983230072969 + 3 ^ 40 * 403493 * 2
def baseEnd_403493 : Nat := 46041299938821125662639

theorem tailTrace_403493 : CollatzResearch.WordTrace tailWord_403493 prefixEnd_403493 46041299938821125662639 := by
  unfold tailWord_403493
  simp only [CollatzResearch.WordTrace]
  refine ⟨14716598727221246963215133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9811065818147497975476755 14716598727221246963215133)
  ·
    refine ⟨5518724522707967611205675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14716598727221246963215133 5518724522707967611205675)
    ·
      refine ⟨8278086784061951416808513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5518724522707967611205675 8278086784061951416808513)
      ·
        refine ⟨6208565088046463562606385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8278086784061951416808513 6208565088046463562606385)
        ·
          refine ⟨4656423816034847671954789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6208565088046463562606385 4656423816034847671954789)
          ·
            refine ⟨873079465506533938491523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4656423816034847671954789 873079465506533938491523)
            ·
              refine ⟨1309619198259800907737285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 873079465506533938491523 1309619198259800907737285)
              ·
                refine ⟨245553599673712670200741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1309619198259800907737285 245553599673712670200741)
                ·
                  refine ⟨46041299938821125662639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 245553599673712670200741 46041299938821125662639)
                  ·
                    rfl

theorem cell22_403493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4, 4].length) (baseStart_403493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403493 prefixEnd_403493 := by exact prefixLift 403493
  have htrace : WordTrace (prefixWord ++ tailWord_403493) baseStart_403493 baseEnd_403493 := by
    simpa [prefixWord, tailWord_403493, baseEnd_403493] using wordTrace_append hprefix tailTrace_403493
  have hstable : (prefixWord ++ tailWord_403493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403493).length < 2 ^ (prefixWord ++ tailWord_403493).sum := by decide
  have hdescent : baseEnd_403493 < baseStart_403493 := by decide
  rcases family_descends (prefixWord ++ tailWord_403493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403542 : List Nat := [5, 2, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_403542 : Nat := 118140960795 + 403542 * 2 ^ 59
def prefixEnd_403542 : Nat := 4983230072969 + 3 ^ 40 * 403542 * 2
def baseEnd_403542 : Nat := 138140673517843582512767

theorem tailTrace_403542 : CollatzResearch.WordTrace tailWord_403542 prefixEnd_403542 138140673517843582512767 := by
  unfold tailWord_403542
  simp only [CollatzResearch.WordTrace]
  refine ⟨919899119002733020734305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9812257269362485554499253 919899119002733020734305)
  ·
    refine ⟨689924339252049765550729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 919899119002733020734305 689924339252049765550729)
    ·
      refine ⟨517443254439037324163047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 689924339252049765550729 517443254439037324163047)
      ·
        refine ⟨776164881658555986244571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517443254439037324163047 776164881658555986244571)
        ·
          refine ⟨1164247322487833979366857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776164881658555986244571 1164247322487833979366857)
          ·
            refine ⟨873185491865875484525143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1164247322487833979366857 873185491865875484525143)
            ·
              refine ⟨1309778237798813226787715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 873185491865875484525143 1309778237798813226787715)
              ·
                refine ⟨1964667356698219840181573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1309778237798813226787715 1964667356698219840181573)
                ·
                  refine ⟨368375129380916220034045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1964667356698219840181573 368375129380916220034045)
                  ·
                    refine ⟨138140673517843582512767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 368375129380916220034045 138140673517843582512767)
                    ·
                      rfl

theorem cell22_403542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_403542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403542 prefixEnd_403542 := by exact prefixLift 403542
  have htrace : WordTrace (prefixWord ++ tailWord_403542) baseStart_403542 baseEnd_403542 := by
    simpa [prefixWord, tailWord_403542, baseEnd_403542] using wordTrace_append hprefix tailTrace_403542
  have hstable : (prefixWord ++ tailWord_403542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403542).length < 2 ^ (prefixWord ++ tailWord_403542).sum := by decide
  have hdescent : baseEnd_403542 < baseStart_403542 := by decide
  rcases family_descends (prefixWord ++ tailWord_403542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403587 : List Nat := [1, 1, 1, 3, 3, 5, 1, 3, 1, 3]
def baseStart_403587 : Nat := 118140960795 + 403587 * 2 ^ 59
def prefixEnd_403587 : Nat := 4983230072969 + 3 ^ 40 * 403587 * 2
def baseEnd_403587 : Nat := 138156077937478465137629

theorem tailTrace_403587 : CollatzResearch.WordTrace tailWord_403587 prefixEnd_403587 138156077937478465137629 := by
  unfold tailWord_403587
  simp only [CollatzResearch.WordTrace]
  refine ⟨14720027188880701017137015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9813351459253800678091343 14720027188880701017137015)
  ·
    refine ⟨22080040783321051525705523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14720027188880701017137015 22080040783321051525705523)
    ·
      refine ⟨33120061174981577288558285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22080040783321051525705523 33120061174981577288558285)
      ·
        refine ⟨12420022940618091483209357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33120061174981577288558285 12420022940618091483209357)
        ·
          refine ⟨4657508602731784306203509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12420022940618091483209357 4657508602731784306203509)
          ·
            refine ⟨436641431506104778706579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4657508602731784306203509 436641431506104778706579)
            ·
              refine ⟨654962147259157168059869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436641431506104778706579 654962147259157168059869)
              ·
                refine ⟨245610805222183938022451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 654962147259157168059869 245610805222183938022451)
                ·
                  refine ⟨368416207833275907033677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 245610805222183938022451 368416207833275907033677)
                  ·
                    refine ⟨138156077937478465137629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 368416207833275907033677 138156077937478465137629)
                    ·
                      rfl

theorem cell22_403587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3, 1, 3].length) (baseStart_403587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403587 prefixEnd_403587 := by exact prefixLift 403587
  have htrace : WordTrace (prefixWord ++ tailWord_403587) baseStart_403587 baseEnd_403587 := by
    simpa [prefixWord, tailWord_403587, baseEnd_403587] using wordTrace_append hprefix tailTrace_403587
  have hstable : (prefixWord ++ tailWord_403587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403587).length < 2 ^ (prefixWord ++ tailWord_403587).sum := by decide
  have hdescent : baseEnd_403587 < baseStart_403587 := by decide
  rcases family_descends (prefixWord ++ tailWord_403587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403596 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 7, 4]
def baseStart_403596 : Nat := 118140960795 + 403596 * 2 ^ 59
def prefixEnd_403596 : Nat := 4983230072969 + 3 ^ 40 * 403596 * 2
def baseEnd_403596 : Nat := 138159158821405441662601

theorem tailTrace_403596 : CollatzResearch.WordTrace tailWord_403596 prefixEnd_403596 138159158821405441662601 := by
  unfold tailWord_403596
  simp only [CollatzResearch.WordTrace]
  refine ⟨7360177722924047777107321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9813570297232063702809761 7360177722924047777107321)
  ·
    refine ⟨5520133292193035832830491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7360177722924047777107321 5520133292193035832830491)
    ·
      refine ⟨8280199938289553749245737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5520133292193035832830491 8280199938289553749245737)
      ·
        refine ⟨6210149953717165311934303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8280199938289553749245737 6210149953717165311934303)
        ·
          refine ⟨9315224930575747967901455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6210149953717165311934303 9315224930575747967901455)
          ·
            refine ⟨13972837395863621951852183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9315224930575747967901455 13972837395863621951852183)
            ·
              refine ⟨20959256093795432927778275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13972837395863621951852183 20959256093795432927778275)
              ·
                refine ⟨31438884140693149391667413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20959256093795432927778275 31438884140693149391667413)
                ·
                  refine ⟨736848847047495688867205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 31438884140693149391667413 736848847047495688867205)
                  ·
                    refine ⟨138159158821405441662601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 736848847047495688867205 138159158821405441662601)
                    ·
                      rfl

theorem cell22_403596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_403596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403596 prefixEnd_403596 := by exact prefixLift 403596
  have htrace : WordTrace (prefixWord ++ tailWord_403596) baseStart_403596 baseEnd_403596 := by
    simpa [prefixWord, tailWord_403596, baseEnd_403596] using wordTrace_append hprefix tailTrace_403596
  have hstable : (prefixWord ++ tailWord_403596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403596).length < 2 ^ (prefixWord ++ tailWord_403596).sum := by decide
  have hdescent : baseEnd_403596 < baseStart_403596 := by decide
  rcases family_descends (prefixWord ++ tailWord_403596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403604 : List Nat := [2, 4, 2, 3, 1, 2, 1, 1, 3, 3]
def baseStart_403604 : Nat := 118140960795 + 403604 * 2 ^ 59
def prefixEnd_403604 : Nat := 4983230072969 + 3 ^ 40 * 403604 * 2
def baseEnd_403604 : Nat := 138161897384896087462577

theorem tailTrace_403604 : CollatzResearch.WordTrace tailWord_403604 prefixEnd_403604 138161897384896087462577 := by
  unfold tailWord_403604
  simp only [CollatzResearch.WordTrace]
  refine ⟨7360323614909556460252933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9813764819879408613670577 7360323614909556460252933)
  ·
    refine ⟨1380060677795541836297425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7360323614909556460252933 1380060677795541836297425)
    ·
      refine ⟨1035045508346656377223069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1380060677795541836297425 1035045508346656377223069)
      ·
        refine ⟨388142065629996141458651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1035045508346656377223069 388142065629996141458651)
        ·
          refine ⟨582213098444994212187977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388142065629996141458651 582213098444994212187977)
          ·
            refine ⟨436659823833745659140983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 582213098444994212187977 436659823833745659140983)
            ·
              refine ⟨654989735750618488711475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436659823833745659140983 654989735750618488711475)
              ·
                refine ⟨982484603625927733067213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654989735750618488711475 982484603625927733067213)
                ·
                  refine ⟨368431726359722899900205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 982484603625927733067213 368431726359722899900205)
                  ·
                    refine ⟨138161897384896087462577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 368431726359722899900205 138161897384896087462577)
                    ·
                      rfl

theorem cell22_403604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_403604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403604 prefixEnd_403604 := by exact prefixLift 403604
  have htrace : WordTrace (prefixWord ++ tailWord_403604) baseStart_403604 baseEnd_403604 := by
    simpa [prefixWord, tailWord_403604, baseEnd_403604] using wordTrace_append hprefix tailTrace_403604
  have hstable : (prefixWord ++ tailWord_403604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403604).length < 2 ^ (prefixWord ++ tailWord_403604).sum := by decide
  have hdescent : baseEnd_403604 < baseStart_403604 := by decide
  rcases family_descends (prefixWord ++ tailWord_403604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403658 : List Nat := [3, 1, 2, 1, 3, 1, 1, 4, 2, 4]
def baseStart_403658 : Nat := 118140960795 + 403658 * 2 ^ 59
def prefixEnd_403658 : Nat := 4983230072969 + 3 ^ 40 * 403658 * 2
def baseEnd_403658 : Nat := 138180382688457946612411

theorem tailTrace_403658 : CollatzResearch.WordTrace tailWord_403658 prefixEnd_403658 138180382688457946612411 := by
  unfold tailWord_403658
  simp only [CollatzResearch.WordTrace]
  refine ⟨3680654192905870035742907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9815077847748986761981085 3680654192905870035742907)
  ·
    refine ⟨5520981289358805053614361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3680654192905870035742907 5520981289358805053614361)
    ·
      refine ⟨4140735967019103790210771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5520981289358805053614361 4140735967019103790210771)
      ·
        refine ⟨6211103950528655685316157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4140735967019103790210771 6211103950528655685316157)
        ·
          refine ⟨2329163981448245881993559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6211103950528655685316157 2329163981448245881993559)
          ·
            refine ⟨3493745972172368822990339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2329163981448245881993559 3493745972172368822990339)
            ·
              refine ⟨5240618958258553234485509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3493745972172368822990339 5240618958258553234485509)
              ·
                refine ⟨982616054673478731466033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5240618958258553234485509 982616054673478731466033)
                ·
                  refine ⟨736962041005109048599525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 982616054673478731466033 736962041005109048599525)
                  ·
                    refine ⟨138180382688457946612411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 736962041005109048599525 138180382688457946612411)
                    ·
                      rfl

theorem cell22_403658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_403658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403658 prefixEnd_403658 := by exact prefixLift 403658
  have htrace : WordTrace (prefixWord ++ tailWord_403658) baseStart_403658 baseEnd_403658 := by
    simpa [prefixWord, tailWord_403658, baseEnd_403658] using wordTrace_append hprefix tailTrace_403658
  have hstable : (prefixWord ++ tailWord_403658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403658).length < 2 ^ (prefixWord ++ tailWord_403658).sum := by decide
  have hdescent : baseEnd_403658 < baseStart_403658 := by decide
  rcases family_descends (prefixWord ++ tailWord_403658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403662 : List Nat := [4, 1, 1, 1, 4, 1, 4, 2, 4]
def baseStart_403662 : Nat := 118140960795 + 403662 * 2 ^ 59
def prefixEnd_403662 : Nat := 4983230072969 + 3 ^ 40 * 403662 * 2
def baseEnd_403662 : Nat := 46060583990067756504133

theorem tailTrace_403662 : CollatzResearch.WordTrace tailWord_403662 prefixEnd_403662 46060583990067756504133 := by
  unfold tailWord_403662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1840345332951123603264655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9815175109072659217411493 1840345332951123603264655)
  ·
    refine ⟨2760517999426685404896983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1840345332951123603264655 2760517999426685404896983)
    ·
      refine ⟨4140776999140028107345475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2760517999426685404896983 4140776999140028107345475)
      ·
        refine ⟨6211165498710042161018213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4140776999140028107345475 6211165498710042161018213)
        ·
          refine ⟨1164593531008132905190915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6211165498710042161018213 1164593531008132905190915)
          ·
            refine ⟨1746890296512199357786373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1164593531008132905190915 1746890296512199357786373)
            ·
              refine ⟨327541930596037379584945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1746890296512199357786373 327541930596037379584945)
              ·
                refine ⟨245656447947028034688709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 327541930596037379584945 245656447947028034688709)
                ·
                  refine ⟨46060583990067756504133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 245656447947028034688709 46060583990067756504133)
                  ·
                    rfl

theorem cell22_403662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_403662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403662 prefixEnd_403662 := by exact prefixLift 403662
  have htrace : WordTrace (prefixWord ++ tailWord_403662) baseStart_403662 baseEnd_403662 := by
    simpa [prefixWord, tailWord_403662, baseEnd_403662] using wordTrace_append hprefix tailTrace_403662
  have hstable : (prefixWord ++ tailWord_403662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403662).length < 2 ^ (prefixWord ++ tailWord_403662).sum := by decide
  have hdescent : baseEnd_403662 < baseStart_403662 := by decide
  rcases family_descends (prefixWord ++ tailWord_403662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403671 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 2, 7]
def baseStart_403671 : Nat := 118140960795 + 403671 * 2 ^ 59
def prefixEnd_403671 : Nat := 4983230072969 + 3 ^ 40 * 403671 * 2
def baseEnd_403671 : Nat := 138184832854130246037371

theorem tailTrace_403671 : CollatzResearch.WordTrace tailWord_403671 prefixEnd_403671 138184832854130246037371 := by
  unfold tailWord_403671
  simp only [CollatzResearch.WordTrace]
  refine ⟨14723090920576383363194867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9815393947050922242129911 14723090920576383363194867)
  ·
    refine ⟨22084636380864575044792301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14723090920576383363194867 22084636380864575044792301)
    ·
      refine ⟨8281738642824215641797113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22084636380864575044792301 8281738642824215641797113)
      ·
        refine ⟨6211303982118161731347835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8281738642824215641797113 6211303982118161731347835)
        ·
          refine ⟨9316955973177242597021753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6211303982118161731347835 9316955973177242597021753)
          ·
            refine ⟨6987716979882931947766315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9316955973177242597021753 6987716979882931947766315)
            ·
              refine ⟨10481575469824397921649473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6987716979882931947766315 10481575469824397921649473)
              ·
                refine ⟨7861181602368298441237105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10481575469824397921649473 7861181602368298441237105)
                ·
                  refine ⟨5895886201776223830927829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7861181602368298441237105 5895886201776223830927829)
                  ·
                    refine ⟨138184832854130246037371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5895886201776223830927829 138184832854130246037371)
                    ·
                      rfl

theorem cell22_403671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_403671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403671 prefixEnd_403671 := by exact prefixLift 403671
  have htrace : WordTrace (prefixWord ++ tailWord_403671) baseStart_403671 baseEnd_403671 := by
    simpa [prefixWord, tailWord_403671, baseEnd_403671] using wordTrace_append hprefix tailTrace_403671
  have hstable : (prefixWord ++ tailWord_403671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403671).length < 2 ^ (prefixWord ++ tailWord_403671).sum := by decide
  have hdescent : baseEnd_403671 < baseStart_403671 := by decide
  rcases family_descends (prefixWord ++ tailWord_403671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403677 : List Nat := [1, 4, 3, 2, 1, 1, 2, 3, 2, 3]
def baseStart_403677 : Nat := 118140960795 + 403677 * 2 ^ 59
def prefixEnd_403677 : Nat := 4983230072969 + 3 ^ 40 * 403677 * 2
def baseEnd_403677 : Nat := 138186886776748230387353

theorem tailTrace_403677 : CollatzResearch.WordTrace tailWord_403677 prefixEnd_403677 138186886776748230387353 := by
  unfold tailWord_403677
  simp only [CollatzResearch.WordTrace]
  refine ⟨14723309758554646387913285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9815539839036430925275523 14723309758554646387913285)
  ·
    refine ⟨2760620579728996197733741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14723309758554646387913285 2760620579728996197733741)
    ·
      refine ⟨1035232717398373574150153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2760620579728996197733741 1035232717398373574150153)
      ·
        refine ⟨776424538048780180612615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1035232717398373574150153 776424538048780180612615)
        ·
          refine ⟨1164636807073170270918923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776424538048780180612615 1164636807073170270918923)
          ·
            refine ⟨1746955210609755406378385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1164636807073170270918923 1746955210609755406378385)
            ·
              refine ⟨1310216407957316554783789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1746955210609755406378385 1310216407957316554783789)
              ·
                refine ⟨491331152983993708043921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1310216407957316554783789 491331152983993708043921)
                ·
                  refine ⟨368498364737995281032941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 491331152983993708043921 368498364737995281032941)
                  ·
                    refine ⟨138186886776748230387353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 368498364737995281032941 138186886776748230387353)
                    ·
                      rfl

theorem cell22_403677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_403677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403677 prefixEnd_403677 := by exact prefixLift 403677
  have htrace : WordTrace (prefixWord ++ tailWord_403677) baseStart_403677 baseEnd_403677 := by
    simpa [prefixWord, tailWord_403677, baseEnd_403677] using wordTrace_append hprefix tailTrace_403677
  have hstable : (prefixWord ++ tailWord_403677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403677).length < 2 ^ (prefixWord ++ tailWord_403677).sum := by decide
  have hdescent : baseEnd_403677 < baseStart_403677 := by decide
  rcases family_descends (prefixWord ++ tailWord_403677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403722 : List Nat := [3, 1, 2, 2, 1, 1, 4, 4, 1, 3]
def baseStart_403722 : Nat := 118140960795 + 403722 * 2 ^ 59
def prefixEnd_403722 : Nat := 4983230072969 + 3 ^ 40 * 403722 * 2
def baseEnd_403722 : Nat := 138202291196383113012215

theorem tailTrace_403722 : CollatzResearch.WordTrace tailWord_403722 prefixEnd_403722 138202291196383113012215 := by
  unfold tailWord_403722
  simp only [CollatzResearch.WordTrace]
  refine ⟨3681237760847904768325355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9816634028927746048867613 3681237760847904768325355)
  ·
    refine ⟨5521856641271857152488033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3681237760847904768325355 5521856641271857152488033)
    ·
      refine ⟨4141392480953892864366025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5521856641271857152488033 4141392480953892864366025)
      ·
        refine ⟨3106044360715419648274519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4141392480953892864366025 3106044360715419648274519)
        ·
          refine ⟨4659066541073129472411779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3106044360715419648274519 4659066541073129472411779)
          ·
            refine ⟨6988599811609694208617669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4659066541073129472411779 6988599811609694208617669)
            ·
              refine ⟨1310362464676817664115813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6988599811609694208617669 1310362464676817664115813)
              ·
                refine ⟨245692962126903312021715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1310362464676817664115813 245692962126903312021715)
                ·
                  refine ⟨368539443190354968032573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 245692962126903312021715 368539443190354968032573)
                  ·
                    refine ⟨138202291196383113012215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 368539443190354968032573 138202291196383113012215)
                    ·
                      rfl

theorem cell22_403722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_403722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403722 prefixEnd_403722 := by exact prefixLift 403722
  have htrace : WordTrace (prefixWord ++ tailWord_403722) baseStart_403722 baseEnd_403722 := by
    simpa [prefixWord, tailWord_403722, baseEnd_403722] using wordTrace_append hprefix tailTrace_403722
  have hstable : (prefixWord ++ tailWord_403722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403722).length < 2 ^ (prefixWord ++ tailWord_403722).sum := by decide
  have hdescent : baseEnd_403722 < baseStart_403722 := by decide
  rcases family_descends (prefixWord ++ tailWord_403722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403733 : List Nat := [1, 3, 2, 1, 2, 1, 4, 1, 2, 5]
def baseStart_403733 : Nat := 118140960795 + 403733 * 2 ^ 59
def prefixEnd_403733 : Nat := 4983230072969 + 3 ^ 40 * 403733 * 2
def baseEnd_403733 : Nat := 138206056721182750987181

theorem tailTrace_403733 : CollatzResearch.WordTrace tailWord_403733 prefixEnd_403733 138206056721182750987181 := by
  unfold tailWord_403733
  simp only [CollatzResearch.WordTrace]
  refine ⟨14725352246351767951951853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9816901497567845301301235 14725352246351767951951853)
  ·
    refine ⟨5522007092381912981981945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14725352246351767951951853 5522007092381912981981945)
    ·
      refine ⟨4141505319286434736486459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5522007092381912981981945 4141505319286434736486459)
      ·
        refine ⟨6212257978929652104729689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4141505319286434736486459 6212257978929652104729689)
        ·
          refine ⟨4659193484197239078547267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6212257978929652104729689 4659193484197239078547267)
          ·
            refine ⟨6988790226295858617820901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4659193484197239078547267 6988790226295858617820901)
            ·
              refine ⟨1310398167430473490841419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6988790226295858617820901 1310398167430473490841419)
              ·
                refine ⟨1965597251145710236262129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1310398167430473490841419 1965597251145710236262129)
                ·
                  refine ⟨1474197938359282677196597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1965597251145710236262129 1474197938359282677196597)
                  ·
                    refine ⟨138206056721182750987181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1474197938359282677196597 138206056721182750987181)
                    ·
                      rfl

theorem cell22_403733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_403733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403733 prefixEnd_403733 := by exact prefixLift 403733
  have htrace : WordTrace (prefixWord ++ tailWord_403733) baseStart_403733 baseEnd_403733 := by
    simpa [prefixWord, tailWord_403733, baseEnd_403733] using wordTrace_append hprefix tailTrace_403733
  have hstable : (prefixWord ++ tailWord_403733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403733).length < 2 ^ (prefixWord ++ tailWord_403733).sum := by decide
  have hdescent : baseEnd_403733 < baseStart_403733 := by decide
  rcases family_descends (prefixWord ++ tailWord_403733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403765 : List Nat := [1, 3, 3, 1, 2, 1, 1, 5, 1, 4]
def baseStart_403765 : Nat := 118140960795 + 403765 * 2 ^ 59
def prefixEnd_403765 : Nat := 4983230072969 + 3 ^ 40 * 403765 * 2
def baseEnd_403765 : Nat := 138217010975145334187083

theorem tailTrace_403765 : CollatzResearch.WordTrace tailWord_403765 prefixEnd_403765 138217010975145334187083 := by
  unfold tailWord_403765
  simp only [CollatzResearch.WordTrace]
  refine ⟨14726519382235837417116749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9817679588157224944744499 14726519382235837417116749)
  ·
    refine ⟨5522444768338439031418781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14726519382235837417116749 5522444768338439031418781)
    ·
      refine ⟨2070916788126914636782043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5522444768338439031418781 2070916788126914636782043)
      ·
        refine ⟨3106375182190371955173065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2070916788126914636782043 3106375182190371955173065)
        ·
          refine ⟨2329781386642778966379799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3106375182190371955173065 2329781386642778966379799)
          ·
            refine ⟨3494672079964168449569699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2329781386642778966379799 3494672079964168449569699)
            ·
              refine ⟨5242008119946252674354549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3494672079964168449569699 5242008119946252674354549)
              ·
                refine ⟨491438261244961188220739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5242008119946252674354549 491438261244961188220739)
                ·
                  refine ⟨737157391867441782331109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 491438261244961188220739 737157391867441782331109)
                  ·
                    refine ⟨138217010975145334187083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 737157391867441782331109 138217010975145334187083)
                    ·
                      rfl

theorem cell22_403765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_403765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403765 prefixEnd_403765 := by exact prefixLift 403765
  have htrace : WordTrace (prefixWord ++ tailWord_403765) baseStart_403765 baseEnd_403765 := by
    simpa [prefixWord, tailWord_403765, baseEnd_403765] using wordTrace_append hprefix tailTrace_403765
  have hstable : (prefixWord ++ tailWord_403765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403765).length < 2 ^ (prefixWord ++ tailWord_403765).sum := by decide
  have hdescent : baseEnd_403765 < baseStart_403765 := by decide
  rcases family_descends (prefixWord ++ tailWord_403765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403829 : List Nat := [1, 3, 4, 1, 2, 2, 2, 2, 2, 3]
def baseStart_403829 : Nat := 118140960795 + 403829 * 2 ^ 59
def prefixEnd_403829 : Nat := 4983230072969 + 3 ^ 40 * 403829 * 2
def baseEnd_403829 : Nat := 138238919483070500586887

theorem tailTrace_403829 : CollatzResearch.WordTrace tailWord_403829 prefixEnd_403829 138238919483070500586887 := by
  unfold tailWord_403829
  simp only [CollatzResearch.WordTrace]
  refine ⟨14728853654003976347446541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9819235769335984231631027 14728853654003976347446541)
  ·
    refine ⟨5523320120251491130292453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14728853654003976347446541 5523320120251491130292453)
    ·
      refine ⟨1035622522547154586929835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5523320120251491130292453 1035622522547154586929835)
      ·
        refine ⟨1553433783820731880394753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1035622522547154586929835 1553433783820731880394753)
        ·
          refine ⟨1165075337865548910296065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1553433783820731880394753 1165075337865548910296065)
          ·
            refine ⟨873806503399161682722049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1165075337865548910296065 873806503399161682722049)
            ·
              refine ⟨655354877549371262041537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 873806503399161682722049 655354877549371262041537)
              ·
                refine ⟨491516158162028446531153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 655354877549371262041537 491516158162028446531153)
                ·
                  refine ⟨368637118621521334898365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 491516158162028446531153 368637118621521334898365)
                  ·
                    refine ⟨138238919483070500586887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 368637118621521334898365 138238919483070500586887)
                    ·
                      rfl

theorem cell22_403829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_403829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403829 prefixEnd_403829 := by exact prefixLift 403829
  have htrace : WordTrace (prefixWord ++ tailWord_403829) baseStart_403829 baseEnd_403829 := by
    simpa [prefixWord, tailWord_403829, baseEnd_403829] using wordTrace_append hprefix tailTrace_403829
  have hstable : (prefixWord ++ tailWord_403829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403829).length < 2 ^ (prefixWord ++ tailWord_403829).sum := by decide
  have hdescent : baseEnd_403829 < baseStart_403829 := by decide
  rcases family_descends (prefixWord ++ tailWord_403829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403930 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 3, 5]
def baseStart_403930 : Nat := 118140960795 + 403930 * 2 ^ 59
def prefixEnd_403930 : Nat := 4983230072969 + 3 ^ 40 * 403930 * 2
def baseEnd_403930 : Nat := 138273493847139903811577

theorem tailTrace_403930 : CollatzResearch.WordTrace tailWord_403930 prefixEnd_403930 138273493847139903811577 := by
  unfold tailWord_403930
  simp only [CollatzResearch.WordTrace]
  refine ⟨3683134356659517649218311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9821691617758713731248829 3683134356659517649218311)
  ·
    refine ⟨5524701534989276473827467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3683134356659517649218311 5524701534989276473827467)
    ·
      refine ⟨8287052302483914710741201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5524701534989276473827467 8287052302483914710741201)
      ·
        refine ⟨6215289226862936033055901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8287052302483914710741201 6215289226862936033055901)
        ·
          refine ⟨2330733460073601012395963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6215289226862936033055901 2330733460073601012395963)
          ·
            refine ⟨3496100190110401518593945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2330733460073601012395963 3496100190110401518593945)
            ·
              refine ⟨2622075142582801138945459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3496100190110401518593945 2622075142582801138945459)
              ·
                refine ⟨3933112713874201708418189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2622075142582801138945459 3933112713874201708418189)
                ·
                  refine ⟨1474917267702825640656821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3933112713874201708418189 1474917267702825640656821)
                  ·
                    refine ⟨138273493847139903811577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1474917267702825640656821 138273493847139903811577)
                    ·
                      rfl

theorem cell22_403930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_403930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403930 prefixEnd_403930 := by exact prefixLift 403930
  have htrace : WordTrace (prefixWord ++ tailWord_403930) baseStart_403930 baseEnd_403930 := by
    simpa [prefixWord, tailWord_403930, baseEnd_403930] using wordTrace_append hprefix tailTrace_403930
  have hstable : (prefixWord ++ tailWord_403930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403930).length < 2 ^ (prefixWord ++ tailWord_403930).sum := by decide
  have hdescent : baseEnd_403930 < baseStart_403930 := by decide
  rcases family_descends (prefixWord ++ tailWord_403930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403947 : List Nat := [1, 1, 1, 1, 2, 3, 4, 4, 2, 3]
def baseStart_403947 : Nat := 118140960795 + 403947 * 2 ^ 59
def prefixEnd_403947 : Nat := 4983230072969 + 3 ^ 40 * 403947 * 2
def baseEnd_403947 : Nat := 138279313294557526136525

theorem tailTrace_403947 : CollatzResearch.WordTrace tailWord_403947 prefixEnd_403947 138279313294557526136525 := by
  unfold tailWord_403947
  simp only [CollatzResearch.WordTrace]
  refine ⟨14733157467576482500242095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9822104978384321666828063 14733157467576482500242095)
  ·
    refine ⟨22099736201364723750363143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14733157467576482500242095 22099736201364723750363143)
    ·
      refine ⟨33149604302047085625544715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22099736201364723750363143 33149604302047085625544715)
      ·
        refine ⟨49724406453070628438317073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33149604302047085625544715 49724406453070628438317073)
        ·
          refine ⟨37293304839802971328737805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49724406453070628438317073 37293304839802971328737805)
          ·
            refine ⟨13984989314926114248276677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37293304839802971328737805 13984989314926114248276677)
            ·
              refine ⟨2622185496548646421551877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13984989314926114248276677 2622185496548646421551877)
              ·
                refine ⟨491659780602871204040977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2622185496548646421551877 491659780602871204040977)
                ·
                  refine ⟨368744835452153403030733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 491659780602871204040977 368744835452153403030733)
                  ·
                    refine ⟨138279313294557526136525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 368744835452153403030733 138279313294557526136525)
                    ·
                      rfl

theorem cell22_403947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 3].length) (baseStart_403947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403947 prefixEnd_403947 := by exact prefixLift 403947
  have htrace : WordTrace (prefixWord ++ tailWord_403947) baseStart_403947 baseEnd_403947 := by
    simpa [prefixWord, tailWord_403947, baseEnd_403947] using wordTrace_append hprefix tailTrace_403947
  have hstable : (prefixWord ++ tailWord_403947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403947).length < 2 ^ (prefixWord ++ tailWord_403947).sum := by decide
  have hdescent : baseEnd_403947 < baseStart_403947 := by decide
  rcases family_descends (prefixWord ++ tailWord_403947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403949 : List Nat := [1, 5, 1, 3, 1, 3, 1, 1, 6]
def baseStart_403949 : Nat := 118140960795 + 403949 * 2 ^ 59
def prefixEnd_403949 : Nat := 4983230072969 + 3 ^ 40 * 403949 * 2
def baseEnd_403949 : Nat := 46093332645143395862173

theorem tailTrace_403949 : CollatzResearch.WordTrace tailWord_403949 prefixEnd_403949 46093332645143395862173 := by
  unfold tailWord_403949
  simp only [CollatzResearch.WordTrace]
  refine ⟨14733230413569236841814901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9822153609046157894543267 14733230413569236841814901)
  ·
    refine ⟨1381240351272115953920147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14733230413569236841814901 1381240351272115953920147)
    ·
      refine ⟨2071860526908173930880221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1381240351272115953920147 2071860526908173930880221)
      ·
        refine ⟨776947697590565224080083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2071860526908173930880221 776947697590565224080083)
        ·
          refine ⟨1165421546385847836120125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776947697590565224080083 1165421546385847836120125)
          ·
            refine ⟨437033079894692938545047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1165421546385847836120125 437033079894692938545047)
            ·
              refine ⟨655549619842039407817571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 437033079894692938545047 655549619842039407817571)
              ·
                refine ⟨983324429763059111726357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 655549619842039407817571 983324429763059111726357)
                ·
                  refine ⟨46093332645143395862173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 983324429763059111726357 46093332645143395862173)
                  ·
                    rfl

theorem cell22_403949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_403949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403949 prefixEnd_403949 := by exact prefixLift 403949
  have htrace : WordTrace (prefixWord ++ tailWord_403949) baseStart_403949 baseEnd_403949 := by
    simpa [prefixWord, tailWord_403949, baseEnd_403949] using wordTrace_append hprefix tailTrace_403949
  have hstable : (prefixWord ++ tailWord_403949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403949).length < 2 ^ (prefixWord ++ tailWord_403949).sum := by decide
  have hdescent : baseEnd_403949 < baseStart_403949 := by decide
  rcases family_descends (prefixWord ++ tailWord_403949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403960 : List Nat := [2, 1, 2, 1, 1, 4, 4, 7]
def baseStart_403960 : Nat := 118140960795 + 403960 * 2 ^ 59
def prefixEnd_403960 : Nat := 4983230072969 + 3 ^ 40 * 403960 * 2
def baseEnd_403960 : Nat := 15364862606692202840165

theorem tailTrace_403960 : CollatzResearch.WordTrace tailWord_403960 prefixEnd_403960 15364862606692202840165 := by
  unfold tailWord_403960
  simp only [CollatzResearch.WordTrace]
  refine ⟨7366815808264692860232667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9822421077686257146976889 7366815808264692860232667)
  ·
    refine ⟨11050223712397039290349001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7366815808264692860232667 11050223712397039290349001)
    ·
      refine ⟨8287667784297779467761751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11050223712397039290349001 8287667784297779467761751)
      ·
        refine ⟨12431501676446669201642627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8287667784297779467761751 12431501676446669201642627)
        ·
          refine ⟨18647252514670003802463941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12431501676446669201642627 18647252514670003802463941)
          ·
            refine ⟨3496359846500625712961989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18647252514670003802463941 3496359846500625712961989)
            ·
              refine ⟨655567471218867321180373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3496359846500625712961989 655567471218867321180373)
              ·
                refine ⟨15364862606692202840165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 655567471218867321180373 15364862606692202840165)
                ·
                  rfl

theorem cell22_403960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 7].length) (baseStart_403960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403960 prefixEnd_403960 := by exact prefixLift 403960
  have htrace : WordTrace (prefixWord ++ tailWord_403960) baseStart_403960 baseEnd_403960 := by
    simpa [prefixWord, tailWord_403960, baseEnd_403960] using wordTrace_append hprefix tailTrace_403960
  have hstable : (prefixWord ++ tailWord_403960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403960).length < 2 ^ (prefixWord ++ tailWord_403960).sum := by decide
  have hdescent : baseEnd_403960 < baseStart_403960 := by decide
  rcases family_descends (prefixWord ++ tailWord_403960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403981 : List Nat := [1, 7, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_403981 : Nat := 118140960795 + 403981 * 2 ^ 59
def prefixEnd_403981 : Nat := 4983230072969 + 3 ^ 40 * 403981 * 2
def baseEnd_403981 : Nat := 138290952189392770786421

theorem tailTrace_403981 : CollatzResearch.WordTrace tailWord_403981 prefixEnd_403981 138290952189392770786421 := by
  unfold tailWord_403981
  simp only [CollatzResearch.WordTrace]
  refine ⟨14734397549453306306979797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9822931699635537537986531 14734397549453306306979797)
  ·
    refine ⟨345337442565311866569839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 14734397549453306306979797 345337442565311866569839)
    ·
      refine ⟨518006163847967799854759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345337442565311866569839 518006163847967799854759)
      ·
        refine ⟨777009245771951699782139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518006163847967799854759 777009245771951699782139)
        ·
          refine ⟨1165513868657927549673209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 777009245771951699782139 1165513868657927549673209)
          ·
            refine ⟨874135401493445662254907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1165513868657927549673209 874135401493445662254907)
            ·
              refine ⟨1311203102240168493382361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874135401493445662254907 1311203102240168493382361)
              ·
                refine ⟨983402326680126370036771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1311203102240168493382361 983402326680126370036771)
                ·
                  refine ⟨1475103490020189555055157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 983402326680126370036771 1475103490020189555055157)
                  ·
                    refine ⟨138290952189392770786421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1475103490020189555055157 138290952189392770786421)
                    ·
                      rfl

theorem cell22_403981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_403981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_403981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_403981 prefixEnd_403981 := by exact prefixLift 403981
  have htrace : WordTrace (prefixWord ++ tailWord_403981) baseStart_403981 baseEnd_403981 := by
    simpa [prefixWord, tailWord_403981, baseEnd_403981] using wordTrace_append hprefix tailTrace_403981
  have hstable : (prefixWord ++ tailWord_403981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403981).length < 2 ^ (prefixWord ++ tailWord_403981).sum := by decide
  have hdescent : baseEnd_403981 < baseStart_403981 := by decide
  rcases family_descends (prefixWord ++ tailWord_403981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404005 : List Nat := [1, 3, 1, 2, 2, 1, 2, 3, 7]
def baseStart_404005 : Nat := 118140960795 + 404005 * 2 ^ 59
def prefixEnd_404005 : Nat := 4983230072969 + 3 ^ 40 * 404005 * 2
def baseEnd_404005 : Nat := 46099722626621569395449

theorem tailTrace_404005 : CollatzResearch.WordTrace tailWord_404005 prefixEnd_404005 46099722626621569395449 := by
  unfold tailWord_404005
  simp only [CollatzResearch.WordTrace]
  refine ⟨14735272901366358405853469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9823515267577572270568979 14735272901366358405853469)
  ·
    refine ⟨5525727338012384402195051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14735272901366358405853469 5525727338012384402195051)
    ·
      refine ⟨8288591007018576603292577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5525727338012384402195051 8288591007018576603292577)
      ·
        refine ⟨6216443255263932452469433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8288591007018576603292577 6216443255263932452469433)
        ·
          refine ⟨4662332441447949339352075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6216443255263932452469433 4662332441447949339352075)
          ·
            refine ⟨6993498662171924009028113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4662332441447949339352075 6993498662171924009028113)
            ·
              refine ⟨5245123996628943006771085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6993498662171924009028113 5245123996628943006771085)
              ·
                refine ⟨1966921498735853627539157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5245123996628943006771085 1966921498735853627539157)
                ·
                  refine ⟨46099722626621569395449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1966921498735853627539157 46099722626621569395449)
                  ·
                    rfl

theorem cell22_404005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 7].length) (baseStart_404005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_404005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_404005 prefixEnd_404005 := by exact prefixLift 404005
  have htrace : WordTrace (prefixWord ++ tailWord_404005) baseStart_404005 baseEnd_404005 := by
    simpa [prefixWord, tailWord_404005, baseEnd_404005] using wordTrace_append hprefix tailTrace_404005
  have hstable : (prefixWord ++ tailWord_404005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404005).length < 2 ^ (prefixWord ++ tailWord_404005).sum := by decide
  have hdescent : baseEnd_404005 < baseStart_404005 := by decide
  rcases family_descends (prefixWord ++ tailWord_404005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404067 : List Nat := [1, 1, 1, 5, 1, 2, 4, 1, 6]
def baseStart_404067 : Nat := 118140960795 + 404067 * 2 ^ 59
def prefixEnd_404067 : Nat := 4983230072969 + 3 ^ 40 * 404067 * 2
def baseEnd_404067 : Nat := 46106797248972404378719

theorem tailTrace_404067 : CollatzResearch.WordTrace tailWord_404067 prefixEnd_404067 46106797248972404378719 := by
  unfold tailWord_404067
  simp only [CollatzResearch.WordTrace]
  refine ⟨14737534227141742994610455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9825022818094495329740303 14737534227141742994610455)
  ·
    refine ⟨22106301340712614491915683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14737534227141742994610455 22106301340712614491915683)
    ·
      refine ⟨33159452011068921737873525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22106301340712614491915683 33159452011068921737873525)
      ·
        refine ⟨3108698626037711412925643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33159452011068921737873525 3108698626037711412925643)
        ·
          refine ⟨4663047939056567119388465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3108698626037711412925643 4663047939056567119388465)
          ·
            refine ⟨3497285954292425339541349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4663047939056567119388465 3497285954292425339541349)
            ·
              refine ⟨655741116429829751164003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3497285954292425339541349 655741116429829751164003)
              ·
                refine ⟨983611674644744626746005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 655741116429829751164003 983611674644744626746005)
                ·
                  refine ⟨46106797248972404378719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 983611674644744626746005 46106797248972404378719)
                  ·
                    rfl

theorem cell22_404067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 6].length) (baseStart_404067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_404067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_404067 prefixEnd_404067 := by exact prefixLift 404067
  have htrace : WordTrace (prefixWord ++ tailWord_404067) baseStart_404067 baseEnd_404067 := by
    simpa [prefixWord, tailWord_404067, baseEnd_404067] using wordTrace_append hprefix tailTrace_404067
  have hstable : (prefixWord ++ tailWord_404067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404067).length < 2 ^ (prefixWord ++ tailWord_404067).sum := by decide
  have hdescent : baseEnd_404067 < baseStart_404067 := by decide
  rcases family_descends (prefixWord ++ tailWord_404067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404097 : List Nat := [1, 2, 4, 2, 1, 1, 1, 3, 1, 6]
def baseStart_404097 : Nat := 118140960795 + 404097 * 2 ^ 59
def prefixEnd_404097 : Nat := 4983230072969 + 3 ^ 40 * 404097 * 2
def baseEnd_404097 : Nat := 138330661360007134886065

theorem tailTrace_404097 : CollatzResearch.WordTrace tailWord_404097 prefixEnd_404097 138330661360007134886065 := by
  unfold tailWord_404097
  simp only [CollatzResearch.WordTrace]
  refine ⟨14738628417033058118202545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9825752278022038745468363 14738628417033058118202545)
  ·
    refine ⟨11053971312774793588651909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14738628417033058118202545 11053971312774793588651909)
    ·
      refine ⟨2072619621145273797872233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11053971312774793588651909 2072619621145273797872233)
      ·
        refine ⟨1554464715858955348404175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2072619621145273797872233 1554464715858955348404175)
        ·
          refine ⟨2331697073788433022606263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1554464715858955348404175 2331697073788433022606263)
          ·
            refine ⟨3497545610682649533909395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2331697073788433022606263 3497545610682649533909395)
            ·
              refine ⟨5246318416023974300864093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3497545610682649533909395 5246318416023974300864093)
              ·
                refine ⟨1967369406008990362824035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5246318416023974300864093 1967369406008990362824035)
                ·
                  refine ⟨2951054109013485544236053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1967369406008990362824035 2951054109013485544236053)
                  ·
                    refine ⟨138330661360007134886065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2951054109013485544236053 138330661360007134886065)
                    ·
                      rfl

theorem cell22_404097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_404097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_404097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_404097 prefixEnd_404097 := by exact prefixLift 404097
  have htrace : WordTrace (prefixWord ++ tailWord_404097) baseStart_404097 baseEnd_404097 := by
    simpa [prefixWord, tailWord_404097, baseEnd_404097] using wordTrace_append hprefix tailTrace_404097
  have hstable : (prefixWord ++ tailWord_404097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404097).length < 2 ^ (prefixWord ++ tailWord_404097).sum := by decide
  have hdescent : baseEnd_404097 < baseStart_404097 := by decide
  rcases family_descends (prefixWord ++ tailWord_404097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
