import V185TrunkScan21Chunk156

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1913032 : List Nat := [2, 1, 3, 1, 2, 1, 1, 6, 4]
def baseStart_1913032 : Nat := 118140960795 + 1913032 * 2 ^ 59
def prefixEnd_1913032 : Nat := 4983230072969 + 3 ^ 40 * 1913032 * 2
def baseEnd_1913032 : Nat := 436579965969806438756503

theorem tailTrace_1913032 : CollatzResearch.WordTrace tailWord_1913032 prefixEnd_1913032 436579965969806438756503 := by
  unfold tailWord_1913032
  simp only [CollatzResearch.WordTrace]
  refine ⟨34887004602709629349606675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46516006136946172466142233 34887004602709629349606675)
  ·
    refine ⟨52330506904064444024410013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34887004602709629349606675 52330506904064444024410013)
    ·
      refine ⟨19623940089024166509153755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52330506904064444024410013 19623940089024166509153755)
      ·
        refine ⟨29435910133536249763730633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19623940089024166509153755 29435910133536249763730633)
        ·
          refine ⟨22076932600152187322797975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29435910133536249763730633 22076932600152187322797975)
          ·
            refine ⟨33115398900228280984196963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22076932600152187322797975 33115398900228280984196963)
            ·
              refine ⟨49673098350342421476295445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33115398900228280984196963 49673098350342421476295445)
              ·
                refine ⟨2328426485172301006701349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49673098350342421476295445 2328426485172301006701349)
                ·
                  refine ⟨436579965969806438756503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2328426485172301006701349 436579965969806438756503)
                  ·
                    rfl

theorem cell21_1913032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 4].length) (baseStart_1913032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1913032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1913032 prefixEnd_1913032 := by exact prefixLift 1913032
  have htrace : WordTrace (prefixWord ++ tailWord_1913032) baseStart_1913032 baseEnd_1913032 := by
    simpa [prefixWord, tailWord_1913032, baseEnd_1913032] using wordTrace_append hprefix tailTrace_1913032
  have hstable : (prefixWord ++ tailWord_1913032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913032).length < 2 ^ (prefixWord ++ tailWord_1913032).sum := by decide
  have hdescent : baseEnd_1913032 < baseStart_1913032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913035 : List Nat := [1, 1, 1, 1, 3, 2, 7, 2, 3]
def baseStart_1913035 : Nat := 118140960795 + 1913035 * 2 ^ 59
def prefixEnd_1913035 : Nat := 4983230072969 + 3 ^ 40 * 1913035 * 2
def baseEnd_1913035 : Nat := 436580650610679100206497

theorem tailTrace_1913035 : CollatzResearch.WordTrace tailWord_1913035 prefixEnd_1913035 436580650610679100206497 := by
  unfold tailWord_1913035
  simp only [CollatzResearch.WordTrace]
  refine ⟨69774118624408390211572559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46516079082938926807715039 69774118624408390211572559)
  ·
    refine ⟨104661177936612585317358839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69774118624408390211572559 104661177936612585317358839)
    ·
      refine ⟨156991766904918877976038259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104661177936612585317358839 156991766904918877976038259)
      ·
        refine ⟨235487650357378316964057389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156991766904918877976038259 235487650357378316964057389)
        ·
          refine ⟨88307868884016868861521521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235487650357378316964057389 88307868884016868861521521)
          ·
            refine ⟨66230901663012651646141141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88307868884016868861521521 66230901663012651646141141)
            ·
              refine ⟨1552286757726859022956433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 66230901663012651646141141 1552286757726859022956433)
              ·
                refine ⟨1164215068295144267217325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1552286757726859022956433 1164215068295144267217325)
                ·
                  refine ⟨436580650610679100206497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1164215068295144267217325 436580650610679100206497)
                  ·
                    rfl

theorem cell21_1913035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2, 3].length) (baseStart_1913035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1913035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1913035 prefixEnd_1913035 := by exact prefixLift 1913035
  have htrace : WordTrace (prefixWord ++ tailWord_1913035) baseStart_1913035 baseEnd_1913035 := by
    simpa [prefixWord, tailWord_1913035, baseEnd_1913035] using wordTrace_append hprefix tailTrace_1913035
  have hstable : (prefixWord ++ tailWord_1913035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913035).length < 2 ^ (prefixWord ++ tailWord_1913035).sum := by decide
  have hdescent : baseEnd_1913035 < baseStart_1913035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913049 : List Nat := [1, 2, 1, 2, 3, 1, 6, 1, 4]
def baseStart_1913049 : Nat := 118140960795 + 1913049 * 2 ^ 59
def prefixEnd_1913049 : Nat := 4983230072969 + 3 ^ 40 * 1913049 * 2
def baseEnd_1913049 : Nat := 436583845601418186973135

theorem tailTrace_1913049 : CollatzResearch.WordTrace tailWord_1913049 prefixEnd_1913049 436583845601418186973135 := by
  unfold tailWord_1913049
  simp only [CollatzResearch.WordTrace]
  refine ⟨69774629246357670602582201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46516419497571780401721467 69774629246357670602582201)
  ·
    refine ⟨52330971934768252951936651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69774629246357670602582201 52330971934768252951936651)
    ·
      refine ⟨78496457902152379427904977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52330971934768252951936651 78496457902152379427904977)
      ·
        refine ⟨58872343426614284570928733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78496457902152379427904977 58872343426614284570928733)
        ·
          refine ⟨22077128784980356714098275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58872343426614284570928733 22077128784980356714098275)
          ·
            refine ⟨33115693177470535071147413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22077128784980356714098275 33115693177470535071147413)
            ·
              refine ⟨1552298117693931331460035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33115693177470535071147413 1552298117693931331460035)
              ·
                refine ⟨2328447176540896997190053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1552298117693931331460035 2328447176540896997190053)
                ·
                  refine ⟨436583845601418186973135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2328447176540896997190053 436583845601418186973135)
                  ·
                    rfl

theorem cell21_1913049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 4].length) (baseStart_1913049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1913049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1913049 prefixEnd_1913049 := by exact prefixLift 1913049
  have htrace : WordTrace (prefixWord ++ tailWord_1913049) baseStart_1913049 baseEnd_1913049 := by
    simpa [prefixWord, tailWord_1913049, baseEnd_1913049] using wordTrace_append hprefix tailTrace_1913049
  have hstable : (prefixWord ++ tailWord_1913049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913049).length < 2 ^ (prefixWord ++ tailWord_1913049).sum := by decide
  have hdescent : baseEnd_1913049 < baseStart_1913049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913063 : List Nat := [1, 1, 5, 3, 1, 1, 2, 7]
def baseStart_1913063 : Nat := 118140960795 + 1913063 * 2 ^ 59
def prefixEnd_1913063 : Nat := 4983230072969 + 3 ^ 40 * 1913063 * 2
def baseEnd_1913063 : Nat := 145529013530719091246591

theorem tailTrace_1913063 : CollatzResearch.WordTrace tailWord_1913063 prefixEnd_1913063 145529013530719091246591 := by
  unfold tailWord_1913063
  simp only [CollatzResearch.WordTrace]
  refine ⟨69775139868306950993591843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46516759912204633995727895 69775139868306950993591843)
  ·
    refine ⟨104662709802460426490387765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69775139868306950993591843 104662709802460426490387765)
    ·
      refine ⟨9812129043980664983473853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104662709802460426490387765 9812129043980664983473853)
      ·
        refine ⟨3679548391492749368802695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9812129043980664983473853 3679548391492749368802695)
        ·
          refine ⟨5519322587239124053204043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3679548391492749368802695 5519322587239124053204043)
          ·
            refine ⟨8278983880858686079806065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5519322587239124053204043 8278983880858686079806065)
            ·
              refine ⟨6209237910644014559854549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8278983880858686079806065 6209237910644014559854549)
              ·
                refine ⟨145529013530719091246591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6209237910644014559854549 145529013530719091246591)
                ·
                  rfl

theorem cell21_1913063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 7].length) (baseStart_1913063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1913063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1913063 prefixEnd_1913063 := by exact prefixLift 1913063
  have htrace : WordTrace (prefixWord ++ tailWord_1913063) baseStart_1913063 baseEnd_1913063 := by
    simpa [prefixWord, tailWord_1913063, baseEnd_1913063] using wordTrace_append hprefix tailTrace_1913063
  have hstable : (prefixWord ++ tailWord_1913063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913063).length < 2 ^ (prefixWord ++ tailWord_1913063).sum := by decide
  have hdescent : baseEnd_1913063 < baseStart_1913063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913128 : List Nat := [2, 1, 5, 1, 3, 1, 2, 3, 3]
def baseStart_1913128 : Nat := 118140960795 + 1913128 * 2 ^ 59
def prefixEnd_1913128 : Nat := 4983230072969 + 3 ^ 40 * 1913128 * 2
def baseEnd_1913128 : Nat := 436601874477731605156307

theorem tailTrace_1913128 : CollatzResearch.WordTrace tailWord_1913128 prefixEnd_1913128 436601874477731605156307 := by
  unfold tailWord_1913128
  simp only [CollatzResearch.WordTrace]
  refine ⟨34888755306535733547354019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46518340408714311396472025 34888755306535733547354019)
  ·
    refine ⟨52333132959803600321031029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34888755306535733547354019 52333132959803600321031029)
    ·
      refine ⟨4906231214981587530096659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52333132959803600321031029 4906231214981587530096659)
      ·
        refine ⟨7359346822472381295144989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4906231214981587530096659 7359346822472381295144989)
        ·
          refine ⟨2759755058427142985679371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7359346822472381295144989 2759755058427142985679371)
          ·
            refine ⟨4139632587640714478519057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2759755058427142985679371 4139632587640714478519057)
            ·
              refine ⟨3104724440730535858889293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4139632587640714478519057 3104724440730535858889293)
              ·
                refine ⟨1164271665273950947083485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3104724440730535858889293 1164271665273950947083485)
                ·
                  refine ⟨436601874477731605156307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1164271665273950947083485 436601874477731605156307)
                  ·
                    rfl

theorem cell21_1913128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3, 3].length) (baseStart_1913128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1913128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1913128 prefixEnd_1913128 := by exact prefixLift 1913128
  have htrace : WordTrace (prefixWord ++ tailWord_1913128) baseStart_1913128 baseEnd_1913128 := by
    simpa [prefixWord, tailWord_1913128, baseEnd_1913128] using wordTrace_append hprefix tailTrace_1913128
  have hstable : (prefixWord ++ tailWord_1913128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913128).length < 2 ^ (prefixWord ++ tailWord_1913128).sum := by decide
  have hdescent : baseEnd_1913128 < baseStart_1913128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913173 : List Nat := [1, 3, 2, 2, 5, 1, 2, 5]
def baseStart_1913173 : Nat := 118140960795 + 1913173 * 2 ^ 59
def prefixEnd_1913173 : Nat := 4983230072969 + 3 ^ 40 * 1913173 * 2
def baseEnd_1913173 : Nat := 145537381363607175635405

theorem tailTrace_1913173 : CollatzResearch.WordTrace tailWord_1913173 prefixEnd_1913173 145537381363607175635405 := by
  unfold tailWord_1913173
  simp only [CollatzResearch.WordTrace]
  refine ⟨69779151897908439780096173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46519434598605626520064115 69779151897908439780096173)
  ·
    refine ⟨26167181961715664917536065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69779151897908439780096173 26167181961715664917536065)
    ·
      refine ⟨19625386471286748688152049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26167181961715664917536065 19625386471286748688152049)
      ·
        refine ⟨14719039853465061516114037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19625386471286748688152049 14719039853465061516114037)
        ·
          refine ⟨1379909986262349517135691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14719039853465061516114037 1379909986262349517135691)
          ·
            refine ⟨2069864979393524275703537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1379909986262349517135691 2069864979393524275703537)
            ·
              refine ⟨1552398734545143206777653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2069864979393524275703537 1552398734545143206777653)
              ·
                refine ⟨145537381363607175635405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1552398734545143206777653 145537381363607175635405)
                ·
                  rfl

theorem cell21_1913173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 5].length) (baseStart_1913173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1913173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1913173 prefixEnd_1913173 := by exact prefixLift 1913173
  have htrace : WordTrace (prefixWord ++ tailWord_1913173) baseStart_1913173 baseEnd_1913173 := by
    simpa [prefixWord, tailWord_1913173, baseEnd_1913173] using wordTrace_append hprefix tailTrace_1913173
  have hstable : (prefixWord ++ tailWord_1913173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913173).length < 2 ^ (prefixWord ++ tailWord_1913173).sum := by decide
  have hdescent : baseEnd_1913173 < baseStart_1913173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913322 : List Nat := [3, 1, 3, 1, 3, 2, 2, 1, 5]
def baseStart_1913322 : Nat := 118140960795 + 1913322 * 2 ^ 59
def prefixEnd_1913322 : Nat := 4983230072969 + 3 ^ 40 * 1913322 * 2
def baseEnd_1913322 : Nat := 436646147920830378922577

theorem tailTrace_1913322 : CollatzResearch.WordTrace tailWord_1913322 prefixEnd_1913322 436646147920830378922577 := by
  unfold tailWord_1913322
  simp only [CollatzResearch.WordTrace]
  refine ⟨17446146593592159556817555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46523057582912425484846813 17446146593592159556817555)
  ·
    refine ⟨26169219890388239335226333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17446146593592159556817555 26169219890388239335226333)
    ·
      refine ⟨9813457458895589750709875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26169219890388239335226333 9813457458895589750709875)
      ·
        refine ⟨14720186188343384626064813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9813457458895589750709875 14720186188343384626064813)
        ·
          refine ⟨5520069820628769234774305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14720186188343384626064813 5520069820628769234774305)
          ·
            refine ⟨4140052365471576926080729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5520069820628769234774305 4140052365471576926080729)
            ·
              refine ⟨3105039274103682694560547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4140052365471576926080729 3105039274103682694560547)
              ·
                refine ⟨4657558911155524041840821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3105039274103682694560547 4657558911155524041840821)
                ·
                  refine ⟨436646147920830378922577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4657558911155524041840821 436646147920830378922577)
                  ·
                    rfl

theorem cell21_1913322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_1913322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1913322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1913322 prefixEnd_1913322 := by exact prefixLift 1913322
  have htrace : WordTrace (prefixWord ++ tailWord_1913322) baseStart_1913322 baseEnd_1913322 := by
    simpa [prefixWord, tailWord_1913322, baseEnd_1913322] using wordTrace_append hprefix tailTrace_1913322
  have hstable : (prefixWord ++ tailWord_1913322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913322).length < 2 ^ (prefixWord ++ tailWord_1913322).sum := by decide
  have hdescent : baseEnd_1913322 < baseStart_1913322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913381 : List Nat := [1, 3, 1, 2, 2, 1, 5, 1, 5]
def baseStart_1913381 : Nat := 118140960795 + 1913381 * 2 ^ 59
def prefixEnd_1913381 : Nat := 4983230072969 + 3 ^ 40 * 1913381 * 2
def baseEnd_1913381 : Nat := 436659612524659387439123

theorem tailTrace_1913381 : CollatzResearch.WordTrace tailWord_1913381 prefixEnd_1913381 436659612524659387439123 := by
  unfold tailWord_1913381
  simp only [CollatzResearch.WordTrace]
  refine ⟨69786738281154891303667997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46524492187436594202445331 69786738281154891303667997)
  ·
    refine ⟨26170026855433084238875499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69786738281154891303667997 26170026855433084238875499)
    ·
      refine ⟨39255040283149626358313249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26170026855433084238875499 39255040283149626358313249)
      ·
        refine ⟨29441280212362219768734937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39255040283149626358313249 29441280212362219768734937)
        ·
          refine ⟨22080960159271664826551203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29441280212362219768734937 22080960159271664826551203)
          ·
            refine ⟨33121440238907497239826805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22080960159271664826551203 33121440238907497239826805)
            ·
              refine ⟨3105135022397577866233763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33121440238907497239826805 3105135022397577866233763)
              ·
                refine ⟨4657702533596366799350645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3105135022397577866233763 4657702533596366799350645)
                ·
                  refine ⟨436659612524659387439123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4657702533596366799350645 436659612524659387439123)
                  ·
                    rfl

theorem cell21_1913381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_1913381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1913381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1913381 prefixEnd_1913381 := by exact prefixLift 1913381
  have htrace : WordTrace (prefixWord ++ tailWord_1913381) baseStart_1913381 baseEnd_1913381 := by
    simpa [prefixWord, tailWord_1913381, baseEnd_1913381] using wordTrace_append hprefix tailTrace_1913381
  have hstable : (prefixWord ++ tailWord_1913381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913381).length < 2 ^ (prefixWord ++ tailWord_1913381).sum := by decide
  have hdescent : baseEnd_1913381 < baseStart_1913381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913519 : List Nat := [1, 1, 2, 1, 2, 7, 2, 5]
def baseStart_1913519 : Nat := 118140960795 + 1913519 * 2 ^ 59
def prefixEnd_1913519 : Nat := 4983230072969 + 3 ^ 40 * 1913519 * 2
def baseEnd_1913519 : Nat := 145563702001600604712947

theorem tailTrace_1913519 : CollatzResearch.WordTrace tailWord_1913519 prefixEnd_1913519 145563702001600604712947 := by
  unfold tailWord_1913519
  simp only [CollatzResearch.WordTrace]
  refine ⟨69791771554654940872191611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46527847703103293914794407 69791771554654940872191611)
  ·
    refine ⟨104687657331982411308287417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69791771554654940872191611 104687657331982411308287417)
    ·
      refine ⟨78515742998986808481215563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104687657331982411308287417 78515742998986808481215563)
      ·
        refine ⟨117773614498480212721823345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78515742998986808481215563 117773614498480212721823345)
        ·
          refine ⟨88330210873860159541367509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117773614498480212721823345 88330210873860159541367509)
          ·
            refine ⟨2070239317356097489250801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 88330210873860159541367509 2070239317356097489250801)
            ·
              refine ⟨1552679488017073116938101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2070239317356097489250801 1552679488017073116938101)
              ·
                refine ⟨145563702001600604712947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1552679488017073116938101 145563702001600604712947)
                ·
                  rfl

theorem cell21_1913519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 5].length) (baseStart_1913519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1913519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1913519 prefixEnd_1913519 := by exact prefixLift 1913519
  have htrace : WordTrace (prefixWord ++ tailWord_1913519) baseStart_1913519 baseEnd_1913519 := by
    simpa [prefixWord, tailWord_1913519, baseEnd_1913519] using wordTrace_append hprefix tailTrace_1913519
  have hstable : (prefixWord ++ tailWord_1913519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913519).length < 2 ^ (prefixWord ++ tailWord_1913519).sum := by decide
  have hdescent : baseEnd_1913519 < baseStart_1913519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913542 : List Nat := [6, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_1913542 : Nat := 118140960795 + 1913542 * 2 ^ 59
def prefixEnd_1913542 : Nat := 4983230072969 + 3 ^ 40 * 1913542 * 2
def baseEnd_1913542 : Nat := 436696354918158885255461

theorem tailTrace_1913542 : CollatzResearch.WordTrace tailWord_1913542 prefixEnd_1913542 436696354918158885255461 := by
  unfold tailWord_1913542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2181019076049112993758715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46528406955714410533519253 2181019076049112993758715)
  ·
    refine ⟨3271528614073669490638073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2181019076049112993758715 3271528614073669490638073)
    ·
      refine ⟨2453646460555252117978555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3271528614073669490638073 2453646460555252117978555)
      ·
        refine ⟨3680469690832878176967833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2453646460555252117978555 3680469690832878176967833)
        ·
          refine ⟨2760352268124658632725875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3680469690832878176967833 2760352268124658632725875)
          ·
            refine ⟨4140528402186987949088813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2760352268124658632725875 4140528402186987949088813)
            ·
              refine ⟨1552698150820120480908305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4140528402186987949088813 1552698150820120480908305)
              ·
                refine ⟨1164523613115090360681229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1552698150820120480908305 1164523613115090360681229)
                ·
                  refine ⟨436696354918158885255461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1164523613115090360681229 436696354918158885255461)
                  ·
                    rfl

theorem cell21_1913542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_1913542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1913542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1913542 prefixEnd_1913542 := by exact prefixLift 1913542
  have htrace : WordTrace (prefixWord ++ tailWord_1913542) baseStart_1913542 baseEnd_1913542 := by
    simpa [prefixWord, tailWord_1913542, baseEnd_1913542] using wordTrace_append hprefix tailTrace_1913542
  have hstable : (prefixWord ++ tailWord_1913542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913542).length < 2 ^ (prefixWord ++ tailWord_1913542).sum := by decide
  have hdescent : baseEnd_1913542 < baseStart_1913542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913550 : List Nat := [4, 1, 1, 1, 3, 4, 1, 1, 5]
def baseStart_1913550 : Nat := 118140960795 + 1913550 * 2 ^ 59
def prefixEnd_1913550 : Nat := 4983230072969 + 3 ^ 40 * 1913550 * 2
def baseEnd_1913550 : Nat := 436698180627152649122111

theorem tailTrace_1913550 : CollatzResearch.WordTrace tailWord_1913550 prefixEnd_1913550 436698180627152649122111 := by
  unfold tailWord_1913550
  simp only [CollatzResearch.WordTrace]
  refine ⟨8724112777192829145821263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46528601478361755444380069 8724112777192829145821263)
  ·
    refine ⟨13086169165789243718731895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8724112777192829145821263 13086169165789243718731895)
    ·
      refine ⟨19629253748683865578097843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13086169165789243718731895 19629253748683865578097843)
      ·
        refine ⟨29443880623025798367146765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19629253748683865578097843 29443880623025798367146765)
        ·
          refine ⟨11041455233634674387680037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29443880623025798367146765 11041455233634674387680037)
          ·
            refine ⟨2070272856306501447690007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11041455233634674387680037 2070272856306501447690007)
            ·
              refine ⟨3105409284459752171535011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2070272856306501447690007 3105409284459752171535011)
              ·
                refine ⟨4658113926689628257302517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3105409284459752171535011 4658113926689628257302517)
                ·
                  refine ⟨436698180627152649122111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4658113926689628257302517 436698180627152649122111)
                  ·
                    rfl

theorem cell21_1913550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_1913550 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1913550 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1913550 prefixEnd_1913550 := by exact prefixLift 1913550
  have htrace : WordTrace (prefixWord ++ tailWord_1913550) baseStart_1913550 baseEnd_1913550 := by
    simpa [prefixWord, tailWord_1913550, baseEnd_1913550] using wordTrace_append hprefix tailTrace_1913550
  have hstable : (prefixWord ++ tailWord_1913550).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913550).length < 2 ^ (prefixWord ++ tailWord_1913550).sum := by decide
  have hdescent : baseEnd_1913550 < baseStart_1913550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913699 : List Nat := [1, 1, 1, 5, 3, 1, 1, 2, 6]
def baseStart_1913699 : Nat := 118140960795 + 1913699 * 2 ^ 59
def prefixEnd_1913699 : Nat := 4983230072969 + 3 ^ 40 * 1913699 * 2
def baseEnd_1913699 : Nat := 436732184457161501138473

theorem tailTrace_1913699 : CollatzResearch.WordTrace tailWord_1913699 prefixEnd_1913699 436732184457161501138473 := by
  unfold tailWord_1913699
  simp only [CollatzResearch.WordTrace]
  refine ⟨69798336694002831613744151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46532224462668554409162767 69798336694002831613744151)
  ·
    refine ⟨104697505041004247420616227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69798336694002831613744151 104697505041004247420616227)
    ·
      refine ⟨157046257561506371130924341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104697505041004247420616227 157046257561506371130924341)
      ·
        refine ⟨14723086646391222293524157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157046257561506371130924341 14723086646391222293524157)
        ·
          refine ⟨5521157492396708360071559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14723086646391222293524157 5521157492396708360071559)
          ·
            refine ⟨8281736238595062540107339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5521157492396708360071559 8281736238595062540107339)
            ·
              refine ⟨12422604357892593810161009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8281736238595062540107339 12422604357892593810161009)
              ·
                refine ⟨9316953268419445357620757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12422604357892593810161009 9316953268419445357620757)
                ·
                  refine ⟨436732184457161501138473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9316953268419445357620757 436732184457161501138473)
                  ·
                    rfl

theorem cell21_1913699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 6].length) (baseStart_1913699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1913699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1913699 prefixEnd_1913699 := by exact prefixLift 1913699
  have htrace : WordTrace (prefixWord ++ tailWord_1913699) baseStart_1913699 baseEnd_1913699 := by
    simpa [prefixWord, tailWord_1913699, baseEnd_1913699] using wordTrace_append hprefix tailTrace_1913699
  have hstable : (prefixWord ++ tailWord_1913699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913699).length < 2 ^ (prefixWord ++ tailWord_1913699).sum := by decide
  have hdescent : baseEnd_1913699 < baseStart_1913699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913713 : List Nat := [1, 2, 2, 2, 1, 4, 9]
def baseStart_1913713 : Nat := 118140960795 + 1913713 * 2 ^ 59
def prefixEnd_1913713 : Nat := 4983230072969 + 3 ^ 40 * 1913713 * 2
def baseEnd_1913713 : Nat := 48526153271988954211679

theorem tailTrace_1913713 : CollatzResearch.WordTrace tailWord_1913713 prefixEnd_1913713 48526153271988954211679 := by
  unfold tailWord_1913713
  simp only [CollatzResearch.WordTrace]
  refine ⟨69798847315952112004753793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46532564877301408003169195 69798847315952112004753793)
  ·
    refine ⟨52349135486964084003565345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69798847315952112004753793 52349135486964084003565345)
    ·
      refine ⟨39261851615223063002674009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52349135486964084003565345 39261851615223063002674009)
      ·
        refine ⟨29446388711417297252005507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39261851615223063002674009 29446388711417297252005507)
        ·
          refine ⟨44169583067125945878008261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29446388711417297252005507 44169583067125945878008261)
          ·
            refine ⟨8281796825086114852126549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44169583067125945878008261 8281796825086114852126549)
            ·
              refine ⟨48526153271988954211679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8281796825086114852126549 48526153271988954211679)
              ·
                rfl

theorem cell21_1913713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 9].length) (baseStart_1913713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1913713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1913713 prefixEnd_1913713 := by exact prefixLift 1913713
  have htrace : WordTrace (prefixWord ++ tailWord_1913713) baseStart_1913713 baseEnd_1913713 := by
    simpa [prefixWord, tailWord_1913713, baseEnd_1913713] using wordTrace_append hprefix tailTrace_1913713
  have hstable : (prefixWord ++ tailWord_1913713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913713).length < 2 ^ (prefixWord ++ tailWord_1913713).sum := by decide
  have hdescent : baseEnd_1913713 < baseStart_1913713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913733 : List Nat := [1, 3, 1, 1, 3, 5, 2, 1, 4]
def baseStart_1913733 : Nat := 118140960795 + 1913733 * 2 ^ 59
def prefixEnd_1913733 : Nat := 4983230072969 + 3 ^ 40 * 1913733 * 2
def baseEnd_1913733 : Nat := 436739943720384997571737

theorem tailTrace_1913733 : CollatzResearch.WordTrace tailWord_1913733 prefixEnd_1913733 436739943720384997571737 := by
  unfold tailWord_1913733
  simp only [CollatzResearch.WordTrace]
  refine ⟨69799576775879655420481853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46533051183919770280321235 69799576775879655420481853)
  ·
    refine ⟨26174841290954870782680695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69799576775879655420481853 26174841290954870782680695)
    ·
      refine ⟨39262261936432306174021043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26174841290954870782680695 39262261936432306174021043)
      ·
        refine ⟨58893392904648459261031565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39262261936432306174021043 58893392904648459261031565)
        ·
          refine ⟨22085022339243172222886837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58893392904648459261031565 22085022339243172222886837)
          ·
            refine ⟨2070470844304047395895641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22085022339243172222886837 2070470844304047395895641)
            ·
              refine ⟨1552853133228035546921731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2070470844304047395895641 1552853133228035546921731)
              ·
                refine ⟨2329279699842053320382597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1552853133228035546921731 2329279699842053320382597)
                ·
                  refine ⟨436739943720384997571737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2329279699842053320382597 436739943720384997571737)
                  ·
                    rfl

theorem cell21_1913733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_1913733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1913733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1913733 prefixEnd_1913733 := by exact prefixLift 1913733
  have htrace : WordTrace (prefixWord ++ tailWord_1913733) baseStart_1913733 baseEnd_1913733 := by
    simpa [prefixWord, tailWord_1913733, baseEnd_1913733] using wordTrace_append hprefix tailTrace_1913733
  have hstable : (prefixWord ++ tailWord_1913733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913733).length < 2 ^ (prefixWord ++ tailWord_1913733).sum := by decide
  have hdescent : baseEnd_1913733 < baseStart_1913733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913826 : List Nat := [3, 3, 3, 1, 1, 3, 1, 2, 4]
def baseStart_1913826 : Nat := 118140960795 + 1913826 * 2 ^ 59
def prefixEnd_1913826 : Nat := 4983230072969 + 3 ^ 40 * 1913826 * 2
def baseEnd_1913826 : Nat := 436761167587437502521547

theorem tailTrace_1913826 : CollatzResearch.WordTrace tailWord_1913826 prefixEnd_1913826 436761167587437502521547 := by
  unfold tailWord_1913826
  simp only [CollatzResearch.WordTrace]
  refine ⟨17450742191135683075904333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46535312509695154869078221 17450742191135683075904333)
  ·
    refine ⟨6544028321675881153464125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17450742191135683075904333 6544028321675881153464125)
    ·
      refine ⟨2454010620628455432549047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6544028321675881153464125 2454010620628455432549047)
      ·
        refine ⟨3681015930942683148823571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2454010620628455432549047 3681015930942683148823571)
        ·
          refine ⟨5521523896414024723235357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3681015930942683148823571 5521523896414024723235357)
          ·
            refine ⟨2070571461155259271213259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5521523896414024723235357 2070571461155259271213259)
            ·
              refine ⟨3105857191732888906819889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2070571461155259271213259 3105857191732888906819889)
              ·
                refine ⟨2329392893799666680114917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3105857191732888906819889 2329392893799666680114917)
                ·
                  refine ⟨436761167587437502521547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2329392893799666680114917 436761167587437502521547)
                  ·
                    rfl

theorem cell21_1913826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_1913826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1913826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1913826 prefixEnd_1913826 := by exact prefixLift 1913826
  have htrace : WordTrace (prefixWord ++ tailWord_1913826) baseStart_1913826 baseEnd_1913826 := by
    simpa [prefixWord, tailWord_1913826, baseEnd_1913826] using wordTrace_append hprefix tailTrace_1913826
  have hstable : (prefixWord ++ tailWord_1913826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913826).length < 2 ^ (prefixWord ++ tailWord_1913826).sum := by decide
  have hdescent : baseEnd_1913826 < baseStart_1913826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913888 : List Nat := [2, 1, 1, 7, 1, 1, 3, 2, 3]
def baseStart_1913888 : Nat := 118140960795 + 1913888 * 2 ^ 59
def prefixEnd_1913888 : Nat := 4983230072969 + 3 ^ 40 * 1913888 * 2
def baseEnd_1913888 : Nat := 436775316832139172488087

theorem tailTrace_1913888 : CollatzResearch.WordTrace tailWord_1913888 prefixEnd_1913888 436775316832139172488087 := by
  unfold tailWord_1913888
  simp only [CollatzResearch.WordTrace]
  refine ⟨34902615045159058446187159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46536820060212077928249545 34902615045159058446187159)
  ·
    refine ⟨52353922567738587669280739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34902615045159058446187159 52353922567738587669280739)
    ·
      refine ⟨78530883851607881503921109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52353922567738587669280739 78530883851607881503921109)
      ·
        refine ⟨1840567590272059722748151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 78530883851607881503921109 1840567590272059722748151)
        ·
          refine ⟨2760851385408089584122227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1840567590272059722748151 2760851385408089584122227)
          ·
            refine ⟨4141277078112134376183341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2760851385408089584122227 4141277078112134376183341)
            ·
              refine ⟨1552978904292050391068753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4141277078112134376183341 1552978904292050391068753)
              ·
                refine ⟨1164734178219037793301565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1552978904292050391068753 1164734178219037793301565)
                ·
                  refine ⟨436775316832139172488087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1164734178219037793301565 436775316832139172488087)
                  ·
                    rfl

theorem cell21_1913888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2, 3].length) (baseStart_1913888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1913888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1913888 prefixEnd_1913888 := by exact prefixLift 1913888
  have htrace : WordTrace (prefixWord ++ tailWord_1913888) baseStart_1913888 baseEnd_1913888 := by
    simpa [prefixWord, tailWord_1913888, baseEnd_1913888] using wordTrace_append hprefix tailTrace_1913888
  have hstable : (prefixWord ++ tailWord_1913888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913888).length < 2 ^ (prefixWord ++ tailWord_1913888).sum := by decide
  have hdescent : baseEnd_1913888 < baseStart_1913888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914003 : List Nat := [1, 1, 1, 2, 1, 2, 7, 2, 4]
def baseStart_1914003 : Nat := 118140960795 + 1914003 * 2 ^ 59
def prefixEnd_1914003 : Nat := 4983230072969 + 3 ^ 40 * 1914003 * 2
def baseEnd_1914003 : Nat := 436801561398924528071185

theorem tailTrace_1914003 : CollatzResearch.WordTrace tailWord_1914003 prefixEnd_1914003 436801561398924528071185 := by
  unfold tailWord_1914003
  simp only [CollatzResearch.WordTrace]
  refine ⟨69809424484901491532810663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46539616323267661021873775 69809424484901491532810663)
  ·
    refine ⟨104714136727352237299215995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69809424484901491532810663 104714136727352237299215995)
    ·
      refine ⟨157071205091028355948823993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104714136727352237299215995 157071205091028355948823993)
      ·
        refine ⟨117803403818271266961617995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157071205091028355948823993 117803403818271266961617995)
        ·
          refine ⟨176705105727406900442426993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117803403818271266961617995 176705105727406900442426993)
          ·
            refine ⟨132528829295555175331820245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176705105727406900442426993 132528829295555175331820245)
            ·
              refine ⟨3106144436614574421839537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 132528829295555175331820245 3106144436614574421839537)
              ·
                refine ⟨2329608327460930816379653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3106144436614574421839537 2329608327460930816379653)
                ·
                  refine ⟨436801561398924528071185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2329608327460930816379653 436801561398924528071185)
                  ·
                    rfl

theorem cell21_1914003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 4].length) (baseStart_1914003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1914003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1914003 prefixEnd_1914003 := by exact prefixLift 1914003
  have htrace : WordTrace (prefixWord ++ tailWord_1914003) baseStart_1914003 baseEnd_1914003 := by
    simpa [prefixWord, tailWord_1914003, baseEnd_1914003] using wordTrace_append hprefix tailTrace_1914003
  have hstable : (prefixWord ++ tailWord_1914003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914003).length < 2 ^ (prefixWord ++ tailWord_1914003).sum := by decide
  have hdescent : baseEnd_1914003 < baseStart_1914003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914017 : List Nat := [1, 2, 3, 3, 1, 1, 2, 8]
def baseStart_1914017 : Nat := 118140960795 + 1914017 * 2 ^ 59
def prefixEnd_1914017 : Nat := 4983230072969 + 3 ^ 40 * 1914017 * 2
def baseEnd_1914017 : Nat := 145601585463221204945941

theorem tailTrace_1914017 : CollatzResearch.WordTrace tailWord_1914017 prefixEnd_1914017 145601585463221204945941 := by
  unfold tailWord_1914017
  simp only [CollatzResearch.WordTrace]
  refine ⟨69809935106850771923820305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46539956737900514615880203 69809935106850771923820305)
  ·
    refine ⟨52357451330138078942865229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69809935106850771923820305 52357451330138078942865229)
    ·
      refine ⟨19634044248801779603574461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52357451330138078942865229 19634044248801779603574461)
      ·
        refine ⟨7362766593300667351340423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19634044248801779603574461 7362766593300667351340423)
        ·
          refine ⟨11044149889951001027010635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7362766593300667351340423 11044149889951001027010635)
          ·
            refine ⟨16566224834926501540515953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11044149889951001027010635 16566224834926501540515953)
            ·
              refine ⟨12424668626194876155386965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16566224834926501540515953 12424668626194876155386965)
              ·
                refine ⟨145601585463221204945941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12424668626194876155386965 145601585463221204945941)
                ·
                  rfl

theorem cell21_1914017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 8].length) (baseStart_1914017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1914017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1914017 prefixEnd_1914017 := by exact prefixLift 1914017
  have htrace : WordTrace (prefixWord ++ tailWord_1914017) baseStart_1914017 baseEnd_1914017 := by
    simpa [prefixWord, tailWord_1914017, baseEnd_1914017] using wordTrace_append hprefix tailTrace_1914017
  have hstable : (prefixWord ++ tailWord_1914017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914017).length < 2 ^ (prefixWord ++ tailWord_1914017).sum := by decide
  have hdescent : baseEnd_1914017 < baseStart_1914017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914034 : List Nat := [3, 2, 1, 1, 1, 4, 4, 5]
def baseStart_1914034 : Nat := 118140960795 + 1914034 * 2 ^ 59
def prefixEnd_1914034 : Nat := 4983230072969 + 3 ^ 40 * 1914034 * 2
def baseEnd_1914034 : Nat := 145602878673758454351485

theorem tailTrace_1914034 : CollatzResearch.WordTrace tailWord_1914034 prefixEnd_1914034 145602878673758454351485 := by
  unfold tailWord_1914034
  simp only [CollatzResearch.WordTrace]
  refine ⟨17452638786947295956797289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46540370098526122551459437 17452638786947295956797289)
  ·
    refine ⟨13089479090210471967597967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17452638786947295956797289 13089479090210471967597967)
    ·
      refine ⟨19634218635315707951396951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13089479090210471967597967 19634218635315707951396951)
      ·
        refine ⟨29451327952973561927095427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19634218635315707951396951 29451327952973561927095427)
        ·
          refine ⟨44176991929460342890643141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29451327952973561927095427 44176991929460342890643141)
          ·
            refine ⟨8283185986773814291995589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44176991929460342890643141 8283185986773814291995589)
            ·
              refine ⟨1553097372520090179749173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8283185986773814291995589 1553097372520090179749173)
              ·
                refine ⟨145602878673758454351485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1553097372520090179749173 145602878673758454351485)
                ·
                  rfl

theorem cell21_1914034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 5].length) (baseStart_1914034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1914034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1914034 prefixEnd_1914034 := by exact prefixLift 1914034
  have htrace : WordTrace (prefixWord ++ tailWord_1914034) baseStart_1914034 baseEnd_1914034 := by
    simpa [prefixWord, tailWord_1914034, baseEnd_1914034] using wordTrace_append hprefix tailTrace_1914034
  have hstable : (prefixWord ++ tailWord_1914034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914034).length < 2 ^ (prefixWord ++ tailWord_1914034).sum := by decide
  have hdescent : baseEnd_1914034 < baseStart_1914034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914141 : List Nat := [1, 4, 2, 3, 1, 2, 1, 2, 5]
def baseStart_1914141 : Nat := 118140960795 + 1914141 * 2 ^ 59
def prefixEnd_1914141 : Nat := 4983230072969 + 3 ^ 40 * 1914141 * 2
def baseEnd_1914141 : Nat := 436833054879066954770903

theorem tailTrace_1914141 : CollatzResearch.WordTrace tailWord_1914141 prefixEnd_1914141 436833054879066954770903 := by
  unfold tailWord_1914141
  simp only [CollatzResearch.WordTrace]
  refine ⟨69814457758401541101334277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46542971838934360734222851 69814457758401541101334277)
  ·
    refine ⟨13090210829700288956500177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69814457758401541101334277 13090210829700288956500177)
    ·
      refine ⟨9817658122275216717375133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13090210829700288956500177 9817658122275216717375133)
      ·
        refine ⟨3681621795853206269015675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9817658122275216717375133 3681621795853206269015675)
        ·
          refine ⟨5522432693779809403523513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3681621795853206269015675 5522432693779809403523513)
          ·
            refine ⟨4141824520334857052642635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5522432693779809403523513 4141824520334857052642635)
            ·
              refine ⟨6212736780502285578963953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4141824520334857052642635 6212736780502285578963953)
              ·
                refine ⟨4659552585376714184222965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6212736780502285578963953 4659552585376714184222965)
                ·
                  refine ⟨436833054879066954770903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4659552585376714184222965 436833054879066954770903)
                  ·
                    rfl

theorem cell21_1914141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_1914141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1914141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1914141 prefixEnd_1914141 := by exact prefixLift 1914141
  have htrace : WordTrace (prefixWord ++ tailWord_1914141) baseStart_1914141 baseEnd_1914141 := by
    simpa [prefixWord, tailWord_1914141, baseEnd_1914141] using wordTrace_append hprefix tailTrace_1914141
  have hstable : (prefixWord ++ tailWord_1914141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914141).length < 2 ^ (prefixWord ++ tailWord_1914141).sum := by decide
  have hdescent : baseEnd_1914141 < baseStart_1914141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914172 : List Nat := [2, 2, 2, 2, 1, 5, 1, 2, 4]
def baseStart_1914172 : Nat := 118140960795 + 1914172 * 2 ^ 59
def prefixEnd_1914172 : Nat := 4983230072969 + 3 ^ 40 * 1914172 * 2
def baseEnd_1914172 : Nat := 436840129501417789754173

theorem tailTrace_1914172 : CollatzResearch.WordTrace tailWord_1914172 prefixEnd_1914172 436840129501417789754173 := by
  unfold tailWord_1914172
  simp only [CollatzResearch.WordTrace]
  refine ⟨34907794210644616697856385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46543725614192822263808513 34907794210644616697856385)
  ·
    refine ⟨26180845657983462523392289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34907794210644616697856385 26180845657983462523392289)
    ·
      refine ⟨19635634243487596892544217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26180845657983462523392289 19635634243487596892544217)
      ·
        refine ⟨14726725682615697669408163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19635634243487596892544217 14726725682615697669408163)
        ·
          refine ⟨22090088523923546504112245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14726725682615697669408163 22090088523923546504112245)
          ·
            refine ⟨2070945799117832484760523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22090088523923546504112245 2070945799117832484760523)
            ·
              refine ⟨3106418698676748727140785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2070945799117832484760523 3106418698676748727140785)
              ·
                refine ⟨2329814024007561545355589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3106418698676748727140785 2329814024007561545355589)
                ·
                  refine ⟨436840129501417789754173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2329814024007561545355589 436840129501417789754173)
                  ·
                    rfl

theorem cell21_1914172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_1914172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1914172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1914172 prefixEnd_1914172 := by exact prefixLift 1914172
  have htrace : WordTrace (prefixWord ++ tailWord_1914172) baseStart_1914172 baseEnd_1914172 := by
    simpa [prefixWord, tailWord_1914172, baseEnd_1914172] using wordTrace_append hprefix tailTrace_1914172
  have hstable : (prefixWord ++ tailWord_1914172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914172).length < 2 ^ (prefixWord ++ tailWord_1914172).sum := by decide
  have hdescent : baseEnd_1914172 < baseStart_1914172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914248 : List Nat := [2, 1, 3, 3, 1, 2, 4, 1, 4]
def baseStart_1914248 : Nat := 118140960795 + 1914248 * 2 ^ 59
def prefixEnd_1914248 : Nat := 4983230072969 + 3 ^ 40 * 1914248 * 2
def baseEnd_1914248 : Nat := 436857473736858546487351

theorem tailTrace_1914248 : CollatzResearch.WordTrace tailWord_1914248 prefixEnd_1914248 436857473736858546487351 := by
  unfold tailWord_1914248
  simp only [CollatzResearch.WordTrace]
  refine ⟨34909180184506949187739699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46545573579342598916986265 34909180184506949187739699)
  ·
    refine ⟨52363770276760423781609549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34909180184506949187739699 52363770276760423781609549)
    ·
      refine ⟨19636413853785158918103581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52363770276760423781609549 19636413853785158918103581)
      ·
        refine ⟨7363655195169434594288843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19636413853785158918103581 7363655195169434594288843)
        ·
          refine ⟨11045482792754151891433265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7363655195169434594288843 11045482792754151891433265)
          ·
            refine ⟨8284112094565613918574949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11045482792754151891433265 8284112094565613918574949)
            ·
              refine ⟨1553271017731052609732803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8284112094565613918574949 1553271017731052609732803)
              ·
                refine ⟨2329906526596578914599205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1553271017731052609732803 2329906526596578914599205)
                ·
                  refine ⟨436857473736858546487351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2329906526596578914599205 436857473736858546487351)
                  ·
                    rfl

theorem cell21_1914248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 4].length) (baseStart_1914248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1914248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1914248 prefixEnd_1914248 := by exact prefixLift 1914248
  have htrace : WordTrace (prefixWord ++ tailWord_1914248) baseStart_1914248 baseEnd_1914248 := by
    simpa [prefixWord, tailWord_1914248, baseEnd_1914248] using wordTrace_append hprefix tailTrace_1914248
  have hstable : (prefixWord ++ tailWord_1914248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914248).length < 2 ^ (prefixWord ++ tailWord_1914248).sum := by decide
  have hdescent : baseEnd_1914248 < baseStart_1914248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914335 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 7]
def baseStart_1914335 : Nat := 118140960795 + 1914335 * 2 ^ 59
def prefixEnd_1914335 : Nat := 4983230072969 + 3 ^ 40 * 1914335 * 2
def baseEnd_1914335 : Nat := 436877328322165728537173

theorem tailTrace_1914335 : CollatzResearch.WordTrace tailWord_1914335 prefixEnd_1914335 436877328322165728537173 := by
  unfold tailWord_1914335
  simp only [CollatzResearch.WordTrace]
  refine ⟨69821533519698712233896459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46547689013132474822597639 69821533519698712233896459)
  ·
    refine ⟨104732300279548068350844689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69821533519698712233896459 104732300279548068350844689)
    ·
      refine ⟨78549225209661051263133517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104732300279548068350844689 78549225209661051263133517)
      ·
        refine ⟨29455959453622894223675069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78549225209661051263133517 29455959453622894223675069)
        ·
          refine ⟨11045984795108585333878151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29455959453622894223675069 11045984795108585333878151)
          ·
            refine ⟨16568977192662878000817227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11045984795108585333878151 16568977192662878000817227)
            ·
              refine ⟨24853465788994317001225841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16568977192662878000817227 24853465788994317001225841)
              ·
                refine ⟨18640099341745737750919381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24853465788994317001225841 18640099341745737750919381)
                ·
                  refine ⟨436877328322165728537173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18640099341745737750919381 436877328322165728537173)
                  ·
                    rfl

theorem cell21_1914335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 7].length) (baseStart_1914335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1914335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1914335 prefixEnd_1914335 := by exact prefixLift 1914335
  have htrace : WordTrace (prefixWord ++ tailWord_1914335) baseStart_1914335 baseEnd_1914335 := by
    simpa [prefixWord, tailWord_1914335, baseEnd_1914335] using wordTrace_append hprefix tailTrace_1914335
  have hstable : (prefixWord ++ tailWord_1914335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914335).length < 2 ^ (prefixWord ++ tailWord_1914335).sum := by decide
  have hdescent : baseEnd_1914335 < baseStart_1914335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914352 : List Nat := [2, 1, 1, 1, 3, 5, 2, 1, 5]
def baseStart_1914352 : Nat := 118140960795 + 1914352 * 2 ^ 59
def prefixEnd_1914352 : Nat := 4983230072969 + 3 ^ 40 * 1914352 * 2
def baseEnd_1914352 : Nat := 436881207953777476753805

theorem tailTrace_1914352 : CollatzResearch.WordTrace tailWord_1914352 prefixEnd_1914352 436881207953777476753805 := by
  unfold tailWord_1914352
  simp only [CollatzResearch.WordTrace]
  refine ⟨34911076780318562068632655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46548102373758082758176873 34911076780318562068632655)
  ·
    refine ⟨52366615170477843102948983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34911076780318562068632655 52366615170477843102948983)
    ·
      refine ⟨78549922755716764654423475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52366615170477843102948983 78549922755716764654423475)
      ·
        refine ⟨117824884133575146981635213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78549922755716764654423475 117824884133575146981635213)
        ·
          refine ⟨44184331550090680118113205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117824884133575146981635213 44184331550090680118113205)
          ·
            refine ⟨4142281082821001261073113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44184331550090680118113205 4142281082821001261073113)
            ·
              refine ⟨3106710812115750945804835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4142281082821001261073113 3106710812115750945804835)
              ·
                refine ⟨4660066218173626418707253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3106710812115750945804835 4660066218173626418707253)
                ·
                  refine ⟨436881207953777476753805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4660066218173626418707253 436881207953777476753805)
                  ·
                    rfl

theorem cell21_1914352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 5].length) (baseStart_1914352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1914352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1914352 prefixEnd_1914352 := by exact prefixLift 1914352
  have htrace : WordTrace (prefixWord ++ tailWord_1914352) baseStart_1914352 baseEnd_1914352 := by
    simpa [prefixWord, tailWord_1914352, baseEnd_1914352] using wordTrace_append hprefix tailTrace_1914352
  have hstable : (prefixWord ++ tailWord_1914352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914352).length < 2 ^ (prefixWord ++ tailWord_1914352).sum := by decide
  have hdescent : baseEnd_1914352 < baseStart_1914352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914372 : List Nat := [2, 3, 2, 3, 3, 1, 2, 5]
def baseStart_1914372 : Nat := 118140960795 + 1914372 * 2 ^ 59
def prefixEnd_1914372 : Nat := 4983230072969 + 3 ^ 40 * 1914372 * 2
def baseEnd_1914372 : Nat := 145628590742087295473477

theorem tailTrace_1914372 : CollatzResearch.WordTrace tailWord_1914372 prefixEnd_1914372 145628590742087295473477 := by
  unfold tailWord_1914372
  simp only [CollatzResearch.WordTrace]
  refine ⟨34911441510282333776496685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46548588680376445035328913 34911441510282333776496685)
  ·
    refine ⟨13091790566355875166186257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34911441510282333776496685 13091790566355875166186257)
    ·
      refine ⟨9818842924766906374639693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13091790566355875166186257 9818842924766906374639693)
      ·
        refine ⟨3682066096787589890489885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9818842924766906374639693 3682066096787589890489885)
        ·
          refine ⟨1380774786295346208933707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3682066096787589890489885 1380774786295346208933707)
          ·
            refine ⟨2071162179443019313400561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1380774786295346208933707 2071162179443019313400561)
            ·
              refine ⟨1553371634582264485050421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2071162179443019313400561 1553371634582264485050421)
              ·
                refine ⟨145628590742087295473477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1553371634582264485050421 145628590742087295473477)
                ·
                  rfl

theorem cell21_1914372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 5].length) (baseStart_1914372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1914372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1914372 prefixEnd_1914372 := by exact prefixLift 1914372
  have htrace : WordTrace (prefixWord ++ tailWord_1914372) baseStart_1914372 baseEnd_1914372 := by
    simpa [prefixWord, tailWord_1914372, baseEnd_1914372] using wordTrace_append hprefix tailTrace_1914372
  have hstable : (prefixWord ++ tailWord_1914372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914372).length < 2 ^ (prefixWord ++ tailWord_1914372).sum := by decide
  have hdescent : baseEnd_1914372 < baseStart_1914372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914414 : List Nat := [4, 1, 3, 1, 2, 2, 2, 6]
def baseStart_1914414 : Nat := 118140960795 + 1914414 * 2 ^ 59
def prefixEnd_1914414 : Nat := 4983230072969 + 3 ^ 40 * 1914414 * 2
def baseEnd_1914414 : Nat := 145631785732826382240115

theorem tailTrace_1914414 : CollatzResearch.WordTrace tailWord_1914414 prefixEnd_1914414 145631785732826382240115 := by
  unfold tailWord_1914414
  simp only [CollatzResearch.WordTrace]
  refine ⟨8728051860801563590752787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46549609924275005817348197 8728051860801563590752787)
  ·
    refine ⟨13092077791202345386129181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8728051860801563590752787 13092077791202345386129181)
    ·
      refine ⟨4909529171700879519798443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13092077791202345386129181 4909529171700879519798443)
      ·
        refine ⟨7364293757551319279697665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4909529171700879519798443 7364293757551319279697665)
        ·
          refine ⟨5523220318163489459773249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7364293757551319279697665 5523220318163489459773249)
          ·
            refine ⟨4142415238622617094829937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5523220318163489459773249 4142415238622617094829937)
            ·
              refine ⟨3106811428966962821122453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4142415238622617094829937 3106811428966962821122453)
              ·
                refine ⟨145631785732826382240115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3106811428966962821122453 145631785732826382240115)
                ·
                  rfl

theorem cell21_1914414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_1914414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1914414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1914414 prefixEnd_1914414 := by exact prefixLift 1914414
  have htrace : WordTrace (prefixWord ++ tailWord_1914414) baseStart_1914414 baseEnd_1914414 := by
    simpa [prefixWord, tailWord_1914414, baseEnd_1914414] using wordTrace_append hprefix tailTrace_1914414
  have hstable : (prefixWord ++ tailWord_1914414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914414).length < 2 ^ (prefixWord ++ tailWord_1914414).sum := by decide
  have hdescent : baseEnd_1914414 < baseStart_1914414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914454 : List Nat := [5, 2, 2, 2, 2, 1, 2, 2, 3]
def baseStart_1914454 : Nat := 118140960795 + 1914454 * 2 ^ 59
def prefixEnd_1914454 : Nat := 4983230072969 + 3 ^ 40 * 1914454 * 2
def baseEnd_1914454 : Nat := 436904485743447966053597

theorem tailTrace_1914454 : CollatzResearch.WordTrace tailWord_1914454 prefixEnd_1914454 436904485743447966053597 := by
  unfold tailWord_1914454
  simp only [CollatzResearch.WordTrace]
  refine ⟨4364117112891724722342401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46550582537511730371652277 4364117112891724722342401)
  ·
    refine ⟨3273087834668793541756801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4364117112891724722342401 3273087834668793541756801)
    ·
      refine ⟨2454815876001595156317601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3273087834668793541756801 2454815876001595156317601)
      ·
        refine ⟨1841111907001196367238201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2454815876001595156317601 1841111907001196367238201)
        ·
          refine ⟨1380833930250897275428651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1841111907001196367238201 1380833930250897275428651)
          ·
            refine ⟨2071250895376345913142977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1380833930250897275428651 2071250895376345913142977)
            ·
              refine ⟨1553438171532259434857233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2071250895376345913142977 1553438171532259434857233)
              ·
                refine ⟨1165078628649194576142925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1553438171532259434857233 1165078628649194576142925)
                ·
                  refine ⟨436904485743447966053597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1165078628649194576142925 436904485743447966053597)
                  ·
                    rfl

theorem cell21_1914454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_1914454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1914454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1914454 prefixEnd_1914454 := by exact prefixLift 1914454
  have htrace : WordTrace (prefixWord ++ tailWord_1914454) baseStart_1914454 baseEnd_1914454 := by
    simpa [prefixWord, tailWord_1914454, baseEnd_1914454] using wordTrace_append hprefix tailTrace_1914454
  have hstable : (prefixWord ++ tailWord_1914454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914454).length < 2 ^ (prefixWord ++ tailWord_1914454).sum := by decide
  have hdescent : baseEnd_1914454 < baseStart_1914454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914631 : List Nat := [1, 1, 4, 4, 2, 2, 2, 2, 3]
def baseStart_1914631 : Nat := 118140960795 + 1914631 * 2 ^ 59
def prefixEnd_1914631 : Nat := 4983230072969 + 3 ^ 40 * 1914631 * 2
def baseEnd_1914631 : Nat := 436944879554934991603235

theorem tailTrace_1914631 : CollatzResearch.WordTrace tailWord_1914631 prefixEnd_1914631 436944879554934991603235 := by
  unfold tailWord_1914631
  simp only [CollatzResearch.WordTrace]
  refine ⟨69832329526626354786671747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46554886351084236524447831 69832329526626354786671747)
  ·
    refine ⟨104748494289939532180007621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69832329526626354786671747 104748494289939532180007621)
    ·
      refine ⟨19640342679363662283751429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104748494289939532180007621 19640342679363662283751429)
      ·
        refine ⟨3682564252380686678203393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19640342679363662283751429 3682564252380686678203393)
        ·
          refine ⟨2761923189285515008652545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3682564252380686678203393 2761923189285515008652545)
          ·
            refine ⟨2071442391964136256489409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2761923189285515008652545 2071442391964136256489409)
            ·
              refine ⟨1553581793973102192367057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2071442391964136256489409 1553581793973102192367057)
              ·
                refine ⟨1165186345479826644275293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1553581793973102192367057 1165186345479826644275293)
                ·
                  refine ⟨436944879554934991603235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1165186345479826644275293 436944879554934991603235)
                  ·
                    rfl

theorem cell21_1914631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2, 3].length) (baseStart_1914631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1914631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1914631 prefixEnd_1914631 := by exact prefixLift 1914631
  have htrace : WordTrace (prefixWord ++ tailWord_1914631) baseStart_1914631 baseEnd_1914631 := by
    simpa [prefixWord, tailWord_1914631, baseEnd_1914631] using wordTrace_append hprefix tailTrace_1914631
  have hstable : (prefixWord ++ tailWord_1914631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914631).length < 2 ^ (prefixWord ++ tailWord_1914631).sum := by decide
  have hdescent : baseEnd_1914631 < baseStart_1914631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914642 : List Nat := [3, 2, 4, 1, 1, 1, 3, 6]
def baseStart_1914642 : Nat := 118140960795 + 1914642 * 2 ^ 59
def prefixEnd_1914642 : Nat := 4983230072969 + 3 ^ 40 * 1914642 * 2
def baseEnd_1914642 : Nat := 145649129968267138973293

theorem tailTrace_1914642 : CollatzResearch.WordTrace tailWord_1914642 prefixEnd_1914642 145649129968267138973293 := by
  unfold tailWord_1914642
  simp only [CollatzResearch.WordTrace]
  refine ⟨17458182682396625916330545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46555153819724335776881453 17458182682396625916330545)
  ·
    refine ⟨13093637011797469437247909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17458182682396625916330545 13093637011797469437247909)
    ·
      refine ⟨2455056939712025519483983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13093637011797469437247909 2455056939712025519483983)
      ·
        refine ⟨3682585409568038279225975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2455056939712025519483983 3682585409568038279225975)
        ·
          refine ⟨5523878114352057418838963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3682585409568038279225975 5523878114352057418838963)
          ·
            refine ⟨8285817171528086128258445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5523878114352057418838963 8285817171528086128258445)
            ·
              refine ⟨3107181439323032298096917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8285817171528086128258445 3107181439323032298096917)
              ·
                refine ⟨145649129968267138973293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3107181439323032298096917 145649129968267138973293)
                ·
                  rfl

theorem cell21_1914642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 6].length) (baseStart_1914642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1914642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1914642 prefixEnd_1914642 := by exact prefixLift 1914642
  have htrace : WordTrace (prefixWord ++ tailWord_1914642) baseStart_1914642 baseEnd_1914642 := by
    simpa [prefixWord, tailWord_1914642, baseEnd_1914642] using wordTrace_append hprefix tailTrace_1914642
  have hstable : (prefixWord ++ tailWord_1914642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914642).length < 2 ^ (prefixWord ++ tailWord_1914642).sum := by decide
  have hdescent : baseEnd_1914642 < baseStart_1914642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914673 : List Nat := [1, 2, 2, 3, 2, 3, 2, 3, 3]
def baseStart_1914673 : Nat := 118140960795 + 1914673 * 2 ^ 59
def prefixEnd_1914673 : Nat := 4983230072969 + 3 ^ 40 * 1914673 * 2
def baseEnd_1914673 : Nat := 436954464527152251903149

theorem tailTrace_1914673 : CollatzResearch.WordTrace tailWord_1914673 prefixEnd_1914673 436954464527152251903149 := by
  unfold tailWord_1914673
  simp only [CollatzResearch.WordTrace]
  refine ⟨69833861392474195959700673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46555907594982797306467115 69833861392474195959700673)
  ·
    refine ⟨52375396044355646969775505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69833861392474195959700673 52375396044355646969775505)
    ·
      refine ⟨39281547033266735227331629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52375396044355646969775505 39281547033266735227331629)
      ·
        refine ⟨14730580137475025710249361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39281547033266735227331629 14730580137475025710249361)
        ·
          refine ⟨11047935103106269282687021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14730580137475025710249361 11047935103106269282687021)
          ·
            refine ⟨4142975663664850981007633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11047935103106269282687021 4142975663664850981007633)
            ·
              refine ⟨3107231747748638235755725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4142975663664850981007633 3107231747748638235755725)
              ·
                refine ⟨1165211905405739338408397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3107231747748638235755725 1165211905405739338408397)
                ·
                  refine ⟨436954464527152251903149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1165211905405739338408397 436954464527152251903149)
                  ·
                    rfl

theorem cell21_1914673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3, 3].length) (baseStart_1914673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1914673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1914673 prefixEnd_1914673 := by exact prefixLift 1914673
  have htrace : WordTrace (prefixWord ++ tailWord_1914673) baseStart_1914673 baseEnd_1914673 := by
    simpa [prefixWord, tailWord_1914673, baseEnd_1914673] using wordTrace_append hprefix tailTrace_1914673
  have hstable : (prefixWord ++ tailWord_1914673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914673).length < 2 ^ (prefixWord ++ tailWord_1914673).sum := by decide
  have hdescent : baseEnd_1914673 < baseStart_1914673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914808 : List Nat := [2, 1, 2, 1, 2, 3, 3, 4, 3]
def baseStart_1914808 : Nat := 118140960795 + 1914808 * 2 ^ 59
def prefixEnd_1914808 : Nat := 4983230072969 + 3 ^ 40 * 1914808 * 2
def baseEnd_1914808 : Nat := 436985273366422017152873

theorem tailTrace_1914808 : CollatzResearch.WordTrace tailWord_1914808 prefixEnd_1914808 436985273366422017152873 := by
  unfold tailWord_1914808
  simp only [CollatzResearch.WordTrace]
  refine ⟨34919392623492557007932539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46559190164656742677243385 34919392623492557007932539)
  ·
    refine ⟨52379088935238835511898809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34919392623492557007932539 52379088935238835511898809)
    ·
      refine ⟨39284316701429126633924107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52379088935238835511898809 39284316701429126633924107)
      ·
        refine ⟨58926475052143689950886161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39284316701429126633924107 58926475052143689950886161)
        ·
          refine ⟨44194856289107767463164621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58926475052143689950886161 44194856289107767463164621)
          ·
            refine ⟨16573071108415412798686733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44194856289107767463164621 16573071108415412798686733)
            ·
              refine ⟨6214901665655779799507525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16573071108415412798686733 6214901665655779799507525)
              ·
                refine ⟨1165294062310458712407661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6214901665655779799507525 1165294062310458712407661)
                ·
                  refine ⟨436985273366422017152873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1165294062310458712407661 436985273366422017152873)
                  ·
                    rfl

theorem cell21_1914808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4, 3].length) (baseStart_1914808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1914808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1914808 prefixEnd_1914808 := by exact prefixLift 1914808
  have htrace : WordTrace (prefixWord ++ tailWord_1914808) baseStart_1914808 baseEnd_1914808 := by
    simpa [prefixWord, tailWord_1914808, baseEnd_1914808] using wordTrace_append hprefix tailTrace_1914808
  have hstable : (prefixWord ++ tailWord_1914808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914808).length < 2 ^ (prefixWord ++ tailWord_1914808).sum := by decide
  have hdescent : baseEnd_1914808 < baseStart_1914808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914893 : List Nat := [1, 7, 1, 2, 2, 1, 1, 3, 3]
def baseStart_1914893 : Nat := 118140960795 + 1914893 * 2 ^ 59
def prefixEnd_1914893 : Nat := 4983230072969 + 3 ^ 40 * 1914893 * 2
def baseEnd_1914893 : Nat := 437004671524480758236033

theorem tailTrace_1914893 : CollatzResearch.WordTrace tailWord_1914893 prefixEnd_1914893 437004671524480758236033 := by
  unfold tailWord_1914893
  simp only [CollatzResearch.WordTrace]
  refine ⟨69841885451677173532709333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46561256967784782355139555 69841885451677173532709333)
  ·
    refine ⟨1636919190273683754672875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 69841885451677173532709333 1636919190273683754672875)
    ·
      refine ⟨2455378785410525632009313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1636919190273683754672875 2455378785410525632009313)
      ·
        refine ⟨1841534089057894224006985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2455378785410525632009313 1841534089057894224006985)
        ·
          refine ⟨1381150566793420668005239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1841534089057894224006985 1381150566793420668005239)
          ·
            refine ⟨2071725850190131002007859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1381150566793420668005239 2071725850190131002007859)
            ·
              refine ⟨3107588775285196503011789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2071725850190131002007859 3107588775285196503011789)
              ·
                refine ⟨1165345790731948688629421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3107588775285196503011789 1165345790731948688629421)
                ·
                  refine ⟨437004671524480758236033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1165345790731948688629421 437004671524480758236033)
                  ·
                    rfl

theorem cell21_1914893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_1914893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1914893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1914893 prefixEnd_1914893 := by exact prefixLift 1914893
  have htrace : WordTrace (prefixWord ++ tailWord_1914893) baseStart_1914893 baseEnd_1914893 := by
    simpa [prefixWord, tailWord_1914893, baseEnd_1914893] using wordTrace_append hprefix tailTrace_1914893
  have hstable : (prefixWord ++ tailWord_1914893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914893).length < 2 ^ (prefixWord ++ tailWord_1914893).sum := by decide
  have hdescent : baseEnd_1914893 < baseStart_1914893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914932 : List Nat := [2, 5, 1, 2, 2, 1, 1, 3, 4]
def baseStart_1914932 : Nat := 118140960795 + 1914932 * 2 ^ 59
def prefixEnd_1914932 : Nat := 4983230072969 + 3 ^ 40 * 1914932 * 2
def baseEnd_1914932 : Nat := 437013571855825357085953

theorem tailTrace_1914932 : CollatzResearch.WordTrace tailWord_1914932 prefixEnd_1914932 437013571855825357085953 := by
  unfold tailWord_1914932
  simp only [CollatzResearch.WordTrace]
  refine ⟨34921653949267941596689525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46562205265690588795586033 34921653949267941596689525)
  ·
    refine ⟨3273905057743869524689643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34921653949267941596689525 3273905057743869524689643)
    ·
      refine ⟨4910857586615804287034465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3273905057743869524689643 4910857586615804287034465)
      ·
        refine ⟨3683143189961853215275849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4910857586615804287034465 3683143189961853215275849)
        ·
          refine ⟨2762357392471389911456887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3683143189961853215275849 2762357392471389911456887)
          ·
            refine ⟨4143536088707084867185331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2762357392471389911456887 4143536088707084867185331)
            ·
              refine ⟨6215304133060627300777997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4143536088707084867185331 6215304133060627300777997)
              ·
                refine ⟨2330739049897735237791749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6215304133060627300777997 2330739049897735237791749)
                ·
                  refine ⟨437013571855825357085953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2330739049897735237791749 437013571855825357085953)
                  ·
                    rfl

theorem cell21_1914932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_1914932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1914932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1914932 prefixEnd_1914932 := by exact prefixLift 1914932
  have htrace : WordTrace (prefixWord ++ tailWord_1914932) baseStart_1914932 baseEnd_1914932 := by
    simpa [prefixWord, tailWord_1914932, baseEnd_1914932] using wordTrace_append hprefix tailTrace_1914932
  have hstable : (prefixWord ++ tailWord_1914932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914932).length < 2 ^ (prefixWord ++ tailWord_1914932).sum := by decide
  have hdescent : baseEnd_1914932 < baseStart_1914932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914988 : List Nat := [2, 2, 1, 1, 3, 3, 3, 6]
def baseStart_1914988 : Nat := 118140960795 + 1914988 * 2 ^ 59
def prefixEnd_1914988 : Nat := 4983230072969 + 3 ^ 40 * 1914988 * 2
def baseEnd_1914988 : Nat := 145675450606260568050835

theorem tailTrace_1914988 : CollatzResearch.WordTrace tailWord_1914988 prefixEnd_1914988 145675450606260568050835 := by
  unfold tailWord_1914988
  simp only [CollatzResearch.WordTrace]
  refine ⟨34922675193166502378708809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46563566924222003171611745 34922675193166502378708809)
  ·
    refine ⟨26192006394874876784031607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34922675193166502378708809 26192006394874876784031607)
    ·
      refine ⟨39288009592312315176047411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26192006394874876784031607 39288009592312315176047411)
      ·
        refine ⟨58932014388468472764071117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39288009592312315176047411 58932014388468472764071117)
        ·
          refine ⟨22099505395675677286526669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58932014388468472764071117 22099505395675677286526669)
          ·
            refine ⟨8287314523378378982447501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22099505395675677286526669 8287314523378378982447501)
            ·
              refine ⟨3107742946266892118417813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8287314523378378982447501 3107742946266892118417813)
              ·
                refine ⟨145675450606260568050835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3107742946266892118417813 145675450606260568050835)
                ·
                  rfl

theorem cell21_1914988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 6].length) (baseStart_1914988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1914988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1914988 prefixEnd_1914988 := by exact prefixLift 1914988
  have htrace : WordTrace (prefixWord ++ tailWord_1914988) baseStart_1914988 baseEnd_1914988 := by
    simpa [prefixWord, tailWord_1914988, baseEnd_1914988] using wordTrace_append hprefix tailTrace_1914988
  have hstable : (prefixWord ++ tailWord_1914988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914988).length < 2 ^ (prefixWord ++ tailWord_1914988).sum := by decide
  have hdescent : baseEnd_1914988 < baseStart_1914988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915005 : List Nat := [1, 4, 1, 1, 3, 3, 3, 5]
def baseStart_1915005 : Nat := 118140960795 + 1915005 * 2 ^ 59
def prefixEnd_1915005 : Nat := 4983230072969 + 3 ^ 40 * 1915005 * 2
def baseEnd_1915005 : Nat := 145676743816797817456379

theorem tailTrace_1915005 : CollatzResearch.WordTrace tailWord_1915005 prefixEnd_1915005 145676743816797817456379 := by
  unfold tailWord_1915005
  simp only [CollatzResearch.WordTrace]
  refine ⟨69845970427271416660786469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46563980284847611107190979 69845970427271416660786469)
  ·
    refine ⟨13096119455113390623897463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69845970427271416660786469 13096119455113390623897463)
    ·
      refine ⟨19644179182670085935846195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13096119455113390623897463 19644179182670085935846195)
      ·
        refine ⟨29466268774005128903769293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19644179182670085935846195 29466268774005128903769293)
        ·
          refine ⟨11049850790251923338913485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29466268774005128903769293 11049850790251923338913485)
          ·
            refine ⟨4143694046344471252092557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11049850790251923338913485 4143694046344471252092557)
            ·
              refine ⟨1553885267379176719534709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4143694046344471252092557 1553885267379176719534709)
              ·
                refine ⟨145676743816797817456379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1553885267379176719534709 145676743816797817456379)
                ·
                  rfl

theorem cell21_1915005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 5].length) (baseStart_1915005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1915005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1915005 prefixEnd_1915005 := by exact prefixLift 1915005
  have htrace : WordTrace (prefixWord ++ tailWord_1915005) baseStart_1915005 baseEnd_1915005 := by
    simpa [prefixWord, tailWord_1915005, baseEnd_1915005] using wordTrace_append hprefix tailTrace_1915005
  have hstable : (prefixWord ++ tailWord_1915005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915005).length < 2 ^ (prefixWord ++ tailWord_1915005).sum := by decide
  have hdescent : baseEnd_1915005 < baseStart_1915005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915036 : List Nat := [2, 2, 3, 2, 1, 1, 1, 6, 3]
def baseStart_1915036 : Nat := 118140960795 + 1915036 * 2 ^ 59
def prefixEnd_1915036 : Nat := 4983230072969 + 3 ^ 40 * 1915036 * 2
def baseEnd_1915036 : Nat := 437037306072744287352407

theorem tailTrace_1915036 : CollatzResearch.WordTrace tailWord_1915036 prefixEnd_1915036 437037306072744287352407 := by
  unfold tailWord_1915036
  simp only [CollatzResearch.WordTrace]
  refine ⟨34923550545079554477582481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46564734060106072636776641 34923550545079554477582481)
  ·
    refine ⟨26192662908809665858186861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34923550545079554477582481 26192662908809665858186861)
    ·
      refine ⟨9822248590803624696820073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26192662908809665858186861 9822248590803624696820073)
      ·
        refine ⟨7366686443102718522615055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9822248590803624696820073 7366686443102718522615055)
        ·
          refine ⟨11050029664654077783922583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7366686443102718522615055 11050029664654077783922583)
          ·
            refine ⟨16575044496981116675883875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11050029664654077783922583 16575044496981116675883875)
            ·
              refine ⟨24862566745471675013825813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16575044496981116675883875 24862566745471675013825813)
              ·
                refine ⟨1165432816193984766273085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24862566745471675013825813 1165432816193984766273085)
                ·
                  refine ⟨437037306072744287352407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1165432816193984766273085 437037306072744287352407)
                  ·
                    rfl

theorem cell21_1915036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6, 3].length) (baseStart_1915036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1915036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1915036 prefixEnd_1915036 := by exact prefixLift 1915036
  have htrace : WordTrace (prefixWord ++ tailWord_1915036) baseStart_1915036 baseEnd_1915036 := by
    simpa [prefixWord, tailWord_1915036, baseEnd_1915036] using wordTrace_append hprefix tailTrace_1915036
  have hstable : (prefixWord ++ tailWord_1915036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915036).length < 2 ^ (prefixWord ++ tailWord_1915036).sum := by decide
  have hdescent : baseEnd_1915036 < baseStart_1915036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915070 : List Nat := [4, 2, 1, 1, 4, 2, 1, 3, 3]
def baseStart_1915070 : Nat := 118140960795 + 1915070 * 2 ^ 59
def prefixEnd_1915070 : Nat := 4983230072969 + 3 ^ 40 * 1915070 * 2
def baseEnd_1915070 : Nat := 437045065335967783785671

theorem tailTrace_1915070 : CollatzResearch.WordTrace tailWord_1915070 prefixEnd_1915070 437045065335967783785671 := by
  unfold tailWord_1915070
  simp only [CollatzResearch.WordTrace]
  refine ⟨8731042646504491595237833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46565560781357288507935109 8731042646504491595237833)
  ·
    refine ⟨6548281984878368696428375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8731042646504491595237833 6548281984878368696428375)
    ·
      refine ⟨9822422977317553044642563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6548281984878368696428375 9822422977317553044642563)
      ·
        refine ⟨14733634465976329566963845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9822422977317553044642563 14733634465976329566963845)
        ·
          refine ⟨2762556462370561793805721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14733634465976329566963845 2762556462370561793805721)
          ·
            refine ⟨2071917346777921345354291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2762556462370561793805721 2071917346777921345354291)
            ·
              refine ⟨3107876020166882018031437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2071917346777921345354291 3107876020166882018031437)
              ·
                refine ⟨1165453507562580756761789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3107876020166882018031437 1165453507562580756761789)
                ·
                  refine ⟨437045065335967783785671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1165453507562580756761789 437045065335967783785671)
                  ·
                    rfl

theorem cell21_1915070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_1915070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1915070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1915070 prefixEnd_1915070 := by exact prefixLift 1915070
  have htrace : WordTrace (prefixWord ++ tailWord_1915070) baseStart_1915070 baseEnd_1915070 := by
    simpa [prefixWord, tailWord_1915070, baseEnd_1915070] using wordTrace_append hprefix tailTrace_1915070
  have hstable : (prefixWord ++ tailWord_1915070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915070).length < 2 ^ (prefixWord ++ tailWord_1915070).sum := by decide
  have hdescent : baseEnd_1915070 < baseStart_1915070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915123 : List Nat := [1, 1, 1, 2, 2, 4, 1, 9]
def baseStart_1915123 : Nat := 118140960795 + 1915123 * 2 ^ 59
def prefixEnd_1915123 : Nat := 4983230072969 + 3 ^ 40 * 1915123 * 2
def baseEnd_1915123 : Nat := 145685720219350489800743

theorem tailTrace_1915123 : CollatzResearch.WordTrace tailWord_1915123 prefixEnd_1915123 145685720219350489800743 := by
  unfold tailWord_1915123
  simp only [CollatzResearch.WordTrace]
  refine ⟨69850274240843922813582023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46566849493895948542388015 69850274240843922813582023)
  ·
    refine ⟨104775411361265884220373035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69850274240843922813582023 104775411361265884220373035)
    ·
      refine ⟨157163117041898826330559553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104775411361265884220373035 157163117041898826330559553)
      ·
        refine ⟨117872337781424119747919665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157163117041898826330559553 117872337781424119747919665)
        ·
          refine ⟨88404253336068089810939749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117872337781424119747919665 88404253336068089810939749)
          ·
            refine ⟨16575797500512766839551203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88404253336068089810939749 16575797500512766839551203)
            ·
              refine ⟨24863696250769150259326805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16575797500512766839551203 24863696250769150259326805)
              ·
                refine ⟨145685720219350489800743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24863696250769150259326805 145685720219350489800743)
                ·
                  rfl

theorem cell21_1915123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 9].length) (baseStart_1915123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1915123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1915123 prefixEnd_1915123 := by exact prefixLift 1915123
  have htrace : WordTrace (prefixWord ++ tailWord_1915123) baseStart_1915123 baseEnd_1915123 := by
    simpa [prefixWord, tailWord_1915123, baseEnd_1915123] using wordTrace_append hprefix tailTrace_1915123
  have hstable : (prefixWord ++ tailWord_1915123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915123).length < 2 ^ (prefixWord ++ tailWord_1915123).sum := by decide
  have hdescent : baseEnd_1915123 < baseStart_1915123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915140 : List Nat := [2, 3, 2, 2, 3, 9]
def baseStart_1915140 : Nat := 118140960795 + 1915140 * 2 ^ 59
def prefixEnd_1915140 : Nat := 4983230072969 + 3 ^ 40 * 1915140 * 2
def baseEnd_1915140 : Nat := 16187445936654193245143

theorem tailTrace_1915140 : CollatzResearch.WordTrace tailWord_1915140 prefixEnd_1915140 16187445936654193245143 := by
  unfold tailWord_1915140
  simp only [CollatzResearch.WordTrace]
  refine ⟨34925447140891167358475437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46567262854521556477967249 34925447140891167358475437)
  ·
    refine ⟨13097042677834187759428289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34925447140891167358475437 13097042677834187759428289)
    ·
      refine ⟨9822782008375640819571217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13097042677834187759428289 9822782008375640819571217)
      ·
        refine ⟨7367086506281730614678413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9822782008375640819571217 7367086506281730614678413)
        ·
          refine ⟨2762657439855648980504405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7367086506281730614678413 2762657439855648980504405)
          ·
            refine ⟨16187445936654193245143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2762657439855648980504405 16187445936654193245143)
            ·
              rfl

theorem cell21_1915140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 9].length) (baseStart_1915140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1915140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1915140 prefixEnd_1915140 := by exact prefixLift 1915140
  have htrace : WordTrace (prefixWord ++ tailWord_1915140) baseStart_1915140 baseEnd_1915140 := by
    simpa [prefixWord, tailWord_1915140, baseEnd_1915140] using wordTrace_append hprefix tailTrace_1915140
  have hstable : (prefixWord ++ tailWord_1915140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915140).length < 2 ^ (prefixWord ++ tailWord_1915140).sum := by decide
  have hdescent : baseEnd_1915140 < baseStart_1915140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915199 : List Nat := [1, 1, 2, 2, 4, 1, 10]
def baseStart_1915199 : Nat := 118140960795 + 1915199 * 2 ^ 59
def prefixEnd_1915199 : Nat := 4983230072969 + 3 ^ 40 * 1915199 * 2
def baseEnd_1915199 : Nat := 48563833877054691792823

theorem tailTrace_1915199 : CollatzResearch.WordTrace tailWord_1915199 prefixEnd_1915199 48563833877054691792823 := by
  unfold tailWord_1915199
  simp only [CollatzResearch.WordTrace]
  refine ⟨69853046188568587793348651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46568697459045725195565767 69853046188568587793348651)
  ·
    refine ⟨104779569282852881690022977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69853046188568587793348651 104779569282852881690022977)
    ·
      refine ⟨78584676962139661267517233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104779569282852881690022977 78584676962139661267517233)
      ·
        refine ⟨58938507721604745950637925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78584676962139661267517233 58938507721604745950637925)
        ·
          refine ⟨11050970197800889865744611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58938507721604745950637925 11050970197800889865744611)
          ·
            refine ⟨16576455296701334798616917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11050970197800889865744611 16576455296701334798616917)
            ·
              refine ⟨48563833877054691792823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16576455296701334798616917 48563833877054691792823)
              ·
                rfl

theorem cell21_1915199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 10].length) (baseStart_1915199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1915199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1915199 prefixEnd_1915199 := by exact prefixLift 1915199
  have htrace : WordTrace (prefixWord ++ tailWord_1915199) baseStart_1915199 baseEnd_1915199 := by
    simpa [prefixWord, tailWord_1915199, baseEnd_1915199] using wordTrace_append hprefix tailTrace_1915199
  have hstable : (prefixWord ++ tailWord_1915199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915199).length < 2 ^ (prefixWord ++ tailWord_1915199).sum := by decide
  have hdescent : baseEnd_1915199 < baseStart_1915199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915247 : List Nat := [1, 1, 2, 1, 3, 1, 2, 7, 3]
def baseStart_1915247 : Nat := 118140960795 + 1915247 * 2 ^ 59
def prefixEnd_1915247 : Nat := 4983230072969 + 3 ^ 40 * 1915247 * 2
def baseEnd_1915247 : Nat := 437085459147454809335309

theorem tailTrace_1915247 : CollatzResearch.WordTrace tailWord_1915247 prefixEnd_1915247 437085459147454809335309 := by
  unfold tailWord_1915247
  simp only [CollatzResearch.WordTrace]
  refine ⟨69854796892394691991095995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46569864594929794660730663 69854796892394691991095995)
  ·
    refine ⟨104782195338592037986643993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69854796892394691991095995 104782195338592037986643993)
    ·
      refine ⟨78586646503944028489982995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104782195338592037986643993 78586646503944028489982995)
      ·
        refine ⟨117879969755916042734974493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78586646503944028489982995 117879969755916042734974493)
        ·
          refine ⟨44204988658468516025615435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117879969755916042734974493 44204988658468516025615435)
          ·
            refine ⟨66307482987702774038423153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44204988658468516025615435 66307482987702774038423153)
            ·
              refine ⟨49730612240777080528817365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66307482987702774038423153 49730612240777080528817365)
              ·
                refine ⟨1165561224393212824894157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 49730612240777080528817365 1165561224393212824894157)
                ·
                  refine ⟨437085459147454809335309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1165561224393212824894157 437085459147454809335309)
                  ·
                    rfl

theorem cell21_1915247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7, 3].length) (baseStart_1915247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1915247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1915247 prefixEnd_1915247 := by exact prefixLift 1915247
  have htrace : WordTrace (prefixWord ++ tailWord_1915247) baseStart_1915247 baseEnd_1915247 := by
    simpa [prefixWord, tailWord_1915247, baseEnd_1915247] using wordTrace_append hprefix tailTrace_1915247
  have hstable : (prefixWord ++ tailWord_1915247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915247).length < 2 ^ (prefixWord ++ tailWord_1915247).sum := by decide
  have hdescent : baseEnd_1915247 < baseStart_1915247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915261 : List Nat := [1, 4, 1, 1, 2, 3, 2, 1, 6]
def baseStart_1915261 : Nat := 118140960795 + 1915261 * 2 ^ 59
def prefixEnd_1915261 : Nat := 4983230072969 + 3 ^ 40 * 1915261 * 2
def baseEnd_1915261 : Nat := 437088654138193896101947

theorem tailTrace_1915261 : CollatzResearch.WordTrace tailWord_1915261 prefixEnd_1915261 437088654138193896101947 := by
  unfold tailWord_1915261
  simp only [CollatzResearch.WordTrace]
  refine ⟨69855307514343972382105637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46570205009562648254737091 69855307514343972382105637)
  ·
    refine ⟨13097870158939494821644807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69855307514343972382105637 13097870158939494821644807)
    ·
      refine ⟨19646805238409242232467211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13097870158939494821644807 19646805238409242232467211)
      ·
        refine ⟨29470207857613863348700817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19646805238409242232467211 29470207857613863348700817)
        ·
          refine ⟨22102655893210397511525613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29470207857613863348700817 22102655893210397511525613)
          ·
            refine ⟨8288495959953899066822105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22102655893210397511525613 8288495959953899066822105)
            ·
              refine ⟨6216371969965424300116579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8288495959953899066822105 6216371969965424300116579)
              ·
                refine ⟨9324557954948136450174869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6216371969965424300116579 9324557954948136450174869)
                ·
                  refine ⟨437088654138193896101947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9324557954948136450174869 437088654138193896101947)
                  ·
                    rfl

theorem cell21_1915261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_1915261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1915261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1915261 prefixEnd_1915261 := by exact prefixLift 1915261
  have htrace : WordTrace (prefixWord ++ tailWord_1915261) baseStart_1915261 baseEnd_1915261 := by
    simpa [prefixWord, tailWord_1915261, baseEnd_1915261] using wordTrace_append hprefix tailTrace_1915261
  have hstable : (prefixWord ++ tailWord_1915261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915261).length < 2 ^ (prefixWord ++ tailWord_1915261).sum := by decide
  have hdescent : baseEnd_1915261 < baseStart_1915261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915275 : List Nat := [1, 1, 1, 1, 4, 4, 1, 8]
def baseStart_1915275 : Nat := 118140960795 + 1915275 * 2 ^ 59
def prefixEnd_1915275 : Nat := 4983230072969 + 3 ^ 40 * 1915275 * 2
def baseEnd_1915275 : Nat := 145697283042977660956195

theorem tailTrace_1915275 : CollatzResearch.WordTrace tailWord_1915275 prefixEnd_1915275 145697283042977660956195 := by
  unfold tailWord_1915275
  simp only [CollatzResearch.WordTrace]
  refine ⟨69855818136293252773115279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46570545424195501848743519 69855818136293252773115279)
  ·
    refine ⟨104783727204439879159672919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69855818136293252773115279 104783727204439879159672919)
    ·
      refine ⟨157175590806659818739509379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104783727204439879159672919 157175590806659818739509379)
      ·
        refine ⟨235763386209989728109264069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157175590806659818739509379 235763386209989728109264069)
        ·
          refine ⟨44205634914373074020487013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235763386209989728109264069 44205634914373074020487013)
          ·
            refine ⟨8288556546444951378841315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44205634914373074020487013 8288556546444951378841315)
            ·
              refine ⟨12432834819667427068261973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8288556546444951378841315 12432834819667427068261973)
              ·
                refine ⟨145697283042977660956195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12432834819667427068261973 145697283042977660956195)
                ·
                  rfl

theorem cell21_1915275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 8].length) (baseStart_1915275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1915275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1915275 prefixEnd_1915275 := by exact prefixLift 1915275
  have htrace : WordTrace (prefixWord ++ tailWord_1915275) baseStart_1915275 baseEnd_1915275 := by
    simpa [prefixWord, tailWord_1915275, baseEnd_1915275] using wordTrace_append hprefix tailTrace_1915275
  have hstable : (prefixWord ++ tailWord_1915275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915275).length < 2 ^ (prefixWord ++ tailWord_1915275).sum := by decide
  have hdescent : baseEnd_1915275 < baseStart_1915275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915309 : List Nat := [1, 5, 2, 2, 3, 8]
def baseStart_1915309 : Nat := 118140960795 + 1915309 * 2 ^ 59
def prefixEnd_1915309 : Nat := 4983230072969 + 3 ^ 40 * 1915309 * 2
def baseEnd_1915309 : Nat := 16188874384894684418587

theorem tailTrace_1915309 : CollatzResearch.WordTrace tailWord_1915309 prefixEnd_1915309 16188874384894684418587 := by
  unfold tailWord_1915309
  simp only [CollatzResearch.WordTrace]
  refine ⟨69857058218170076579852981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46571372145446717719901987 69857058218170076579852981)
  ·
    refine ⟨6549099207953444679361217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69857058218170076579852981 6549099207953444679361217)
    ·
      refine ⟨4911824405965083509520913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6549099207953444679361217 4911824405965083509520913)
      ·
        refine ⟨3683868304473812632140685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4911824405965083509520913 3683868304473812632140685)
        ·
          refine ⟨1381450614177679737052757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3683868304473812632140685 1381450614177679737052757)
          ·
            refine ⟨16188874384894684418587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1381450614177679737052757 16188874384894684418587)
            ·
              rfl

theorem cell21_1915309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 8].length) (baseStart_1915309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1915309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1915309 prefixEnd_1915309 := by exact prefixLift 1915309
  have htrace : WordTrace (prefixWord ++ tailWord_1915309) baseStart_1915309 baseEnd_1915309 := by
    simpa [prefixWord, tailWord_1915309, baseEnd_1915309] using wordTrace_append hprefix tailTrace_1915309
  have hstable : (prefixWord ++ tailWord_1915309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915309).length < 2 ^ (prefixWord ++ tailWord_1915309).sum := by decide
  have hdescent : baseEnd_1915309 < baseStart_1915309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915337 : List Nat := [1, 2, 1, 1, 2, 1, 6, 3, 4]
def baseStart_1915337 : Nat := 118140960795 + 1915337 * 2 ^ 59
def prefixEnd_1915337 : Nat := 4983230072969 + 3 ^ 40 * 1915337 * 2
def baseEnd_1915337 : Nat := 437105998373634652835125

theorem tailTrace_1915337 : CollatzResearch.WordTrace tailWord_1915337 prefixEnd_1915337 437105998373634652835125 := by
  unfold tailWord_1915337
  simp only [CollatzResearch.WordTrace]
  refine ⟨69858079462068637361872265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46572052974712424907914843 69858079462068637361872265)
  ·
    refine ⟨52393559596551478021404199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69858079462068637361872265 52393559596551478021404199)
    ·
      refine ⟨78590339394827217032106299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52393559596551478021404199 78590339394827217032106299)
      ·
        refine ⟨117885509092240825548159449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78590339394827217032106299 117885509092240825548159449)
        ·
          refine ⟨88414131819180619161119587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117885509092240825548159449 88414131819180619161119587)
          ·
            refine ⟨132621197728770928741679381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88414131819180619161119587 132621197728770928741679381)
            ·
              refine ⟨6216618643536137284766221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 132621197728770928741679381 6216618643536137284766221)
              ·
                refine ⟨2331231991326051481787333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6216618643536137284766221 2331231991326051481787333)
                ·
                  refine ⟨437105998373634652835125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2331231991326051481787333 437105998373634652835125)
                  ·
                    rfl

theorem cell21_1915337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 4].length) (baseStart_1915337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1915337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1915337 prefixEnd_1915337 := by exact prefixLift 1915337
  have htrace : WordTrace (prefixWord ++ tailWord_1915337) baseStart_1915337 baseEnd_1915337 := by
    simpa [prefixWord, tailWord_1915337, baseEnd_1915337] using wordTrace_append hprefix tailTrace_1915337
  have hstable : (prefixWord ++ tailWord_1915337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915337).length < 2 ^ (prefixWord ++ tailWord_1915337).sum := by decide
  have hdescent : baseEnd_1915337 < baseStart_1915337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915416 : List Nat := [2, 1, 2, 3, 3, 1, 3, 3, 3]
def baseStart_1915416 : Nat := 118140960795 + 1915416 * 2 ^ 59
def prefixEnd_1915416 : Nat := 4983230072969 + 3 ^ 40 * 1915416 * 2
def baseEnd_1915416 : Nat := 437124027249948071018297

theorem tailTrace_1915416 : CollatzResearch.WordTrace tailWord_1915416 prefixEnd_1915416 437124027249948071018297 := by
  unfold tailWord_1915416
  simp only [CollatzResearch.WordTrace]
  refine ⟨34930480414391216926999051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46573973885854955902665401 34930480414391216926999051)
  ·
    refine ⟨52395720621586825390498577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34930480414391216926999051 52395720621586825390498577)
    ·
      refine ⟨39296790466190119042873933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52395720621586825390498577 39296790466190119042873933)
      ·
        refine ⟨14736296424821294641077725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39296790466190119042873933 14736296424821294641077725)
        ·
          refine ⟨5526111159307985490404147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14736296424821294641077725 5526111159307985490404147)
          ·
            refine ⟨8289166738961978235606221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5526111159307985490404147 8289166738961978235606221)
            ·
              refine ⟨3108437527110741838352333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8289166738961978235606221 3108437527110741838352333)
              ·
                refine ⟨1165664072666528189382125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3108437527110741838352333 1165664072666528189382125)
                ·
                  refine ⟨437124027249948071018297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1165664072666528189382125 437124027249948071018297)
                  ·
                    rfl

theorem cell21_1915416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3, 3].length) (baseStart_1915416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1915416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1915416 prefixEnd_1915416 := by exact prefixLift 1915416
  have htrace : WordTrace (prefixWord ++ tailWord_1915416) baseStart_1915416 baseEnd_1915416 := by
    simpa [prefixWord, tailWord_1915416, baseEnd_1915416] using wordTrace_append hprefix tailTrace_1915416
  have hstable : (prefixWord ++ tailWord_1915416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915416).length < 2 ^ (prefixWord ++ tailWord_1915416).sum := by decide
  have hdescent : baseEnd_1915416 < baseStart_1915416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915427 : List Nat := [1, 1, 1, 4, 4, 1, 9]
def baseStart_1915427 : Nat := 118140960795 + 1915427 * 2 ^ 59
def prefixEnd_1915427 : Nat := 4983230072969 + 3 ^ 40 * 1915427 * 2
def baseEnd_1915427 : Nat := 48569615288868277370549

theorem tailTrace_1915427 : CollatzResearch.WordTrace tailWord_1915427 prefixEnd_1915427 48569615288868277370549 := by
  unfold tailWord_1915427
  simp only [CollatzResearch.WordTrace]
  refine ⟨69861362031742582732648535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46574241354495055155099023 69861362031742582732648535)
  ·
    refine ⟨104792043047613874098972803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69861362031742582732648535 104792043047613874098972803)
    ·
      refine ⟨157188064571420811148459205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104792043047613874098972803 157188064571420811148459205)
      ·
        refine ⟨29472762107141402090336101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157188064571420811148459205 29472762107141402090336101)
        ·
          refine ⟨5526142895089012891938019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29472762107141402090336101 5526142895089012891938019)
          ·
            refine ⟨8289214342633519337907029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5526142895089012891938019 8289214342633519337907029)
            ·
              refine ⟨48569615288868277370549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8289214342633519337907029 48569615288868277370549)
              ·
                rfl

theorem cell21_1915427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 9].length) (baseStart_1915427 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1915427 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1915427 prefixEnd_1915427 := by exact prefixLift 1915427
  have htrace : WordTrace (prefixWord ++ tailWord_1915427) baseStart_1915427 baseEnd_1915427 := by
    simpa [prefixWord, tailWord_1915427, baseEnd_1915427] using wordTrace_append hprefix tailTrace_1915427
  have hstable : (prefixWord ++ tailWord_1915427).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915427).length < 2 ^ (prefixWord ++ tailWord_1915427).sum := by decide
  have hdescent : baseEnd_1915427 < baseStart_1915427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915472 : List Nat := [2, 1, 1, 1, 1, 3, 2, 4, 6]
def baseStart_1915472 : Nat := 118140960795 + 1915472 * 2 ^ 59
def prefixEnd_1915472 : Nat := 4983230072969 + 3 ^ 40 * 1915472 * 2
def baseEnd_1915472 : Nat := 437136807212904418084849

theorem tailTrace_1915472 : CollatzResearch.WordTrace tailWord_1915472 prefixEnd_1915472 437136807212904418084849 := by
  unfold tailWord_1915472
  simp only [CollatzResearch.WordTrace]
  refine ⟨34931501658289777709018335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46575335544386370278691113 34931501658289777709018335)
  ·
    refine ⟨52397252487434666563527503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34931501658289777709018335 52397252487434666563527503)
    ·
      refine ⟨78595878731151999845291255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52397252487434666563527503 78595878731151999845291255)
      ·
        refine ⟨117893818096727999767936883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78595878731151999845291255 117893818096727999767936883)
        ·
          refine ⟨176840727145091999651905325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117893818096727999767936883 176840727145091999651905325)
          ·
            refine ⟨66315272679409499869464497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176840727145091999651905325 66315272679409499869464497)
            ·
              refine ⟨49736454509557124902098373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66315272679409499869464497 49736454509557124902098373)
              ·
                refine ⟨9325585220541960919143445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49736454509557124902098373 9325585220541960919143445)
                ·
                  refine ⟨437136807212904418084849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9325585220541960919143445 437136807212904418084849)
                  ·
                    rfl

theorem cell21_1915472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 6].length) (baseStart_1915472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1915472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1915472 prefixEnd_1915472 := by exact prefixLift 1915472
  have htrace : WordTrace (prefixWord ++ tailWord_1915472) baseStart_1915472 baseEnd_1915472 := by
    simpa [prefixWord, tailWord_1915472, baseEnd_1915472] using wordTrace_append hprefix tailTrace_1915472
  have hstable : (prefixWord ++ tailWord_1915472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915472).length < 2 ^ (prefixWord ++ tailWord_1915472).sum := by decide
  have hdescent : baseEnd_1915472 < baseStart_1915472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915489 : List Nat := [1, 2, 3, 1, 1, 4, 1, 4, 4]
def baseStart_1915489 : Nat := 118140960795 + 1915489 * 2 ^ 59
def prefixEnd_1915489 : Nat := 4983230072969 + 3 ^ 40 * 1915489 * 2
def baseEnd_1915489 : Nat := 437140686844516166301481

theorem tailTrace_1915489 : CollatzResearch.WordTrace tailWord_1915489 prefixEnd_1915489 437140686844516166301481 := by
  unfold tailWord_1915489
  simp only [CollatzResearch.WordTrace]
  refine ⟨69863623357517967321405521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46575748905011978214270347 69863623357517967321405521)
  ·
    refine ⟨52397717518138475491054141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69863623357517967321405521 52397717518138475491054141)
    ·
      refine ⟨19649144069301928309145303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52397717518138475491054141 19649144069301928309145303)
      ·
        refine ⟨29473716103952892463717955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19649144069301928309145303 29473716103952892463717955)
        ·
          refine ⟨44210574155929338695576933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29473716103952892463717955 44210574155929338695576933)
          ·
            refine ⟨8289482654236751005420675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44210574155929338695576933 8289482654236751005420675)
            ·
              refine ⟨12434223981355126508131013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8289482654236751005420675 12434223981355126508131013)
              ·
                refine ⟨2331416996504086220274565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12434223981355126508131013 2331416996504086220274565)
                ·
                  refine ⟨437140686844516166301481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2331416996504086220274565 437140686844516166301481)
                  ·
                    rfl

theorem cell21_1915489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 4].length) (baseStart_1915489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1915489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1915489 prefixEnd_1915489 := by exact prefixLift 1915489
  have htrace : WordTrace (prefixWord ++ tailWord_1915489) baseStart_1915489 baseEnd_1915489 := by
    simpa [prefixWord, tailWord_1915489, baseEnd_1915489] using wordTrace_append hprefix tailTrace_1915489
  have hstable : (prefixWord ++ tailWord_1915489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915489).length < 2 ^ (prefixWord ++ tailWord_1915489).sum := by decide
  have hdescent : baseEnd_1915489 < baseStart_1915489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915503 : List Nat := [1, 1, 2, 1, 3, 2, 5, 6]
def baseStart_1915503 : Nat := 118140960795 + 1915503 * 2 ^ 59
def prefixEnd_1915503 : Nat := 4983230072969 + 3 ^ 40 * 1915503 * 2
def baseEnd_1915503 : Nat := 145714627278418417689373

theorem tailTrace_1915503 : CollatzResearch.WordTrace tailWord_1915503 prefixEnd_1915503 145714627278418417689373 := by
  unfold tailWord_1915503
  simp only [CollatzResearch.WordTrace]
  refine ⟨69864133979467247712415163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46576089319644831808276775 69864133979467247712415163)
  ·
    refine ⟨104796200969200871568622745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69864133979467247712415163 104796200969200871568622745)
    ·
      refine ⟨78597150726900653676467059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104796200969200871568622745 78597150726900653676467059)
      ·
        refine ⟨117895726090350980514700589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78597150726900653676467059 117895726090350980514700589)
        ·
          refine ⟨44210897283881617693012721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117895726090350980514700589 44210897283881617693012721)
          ·
            refine ⟨33158172962911213269759541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44210897283881617693012721 33158172962911213269759541)
            ·
              refine ⟨3108578715272926244039957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33158172962911213269759541 3108578715272926244039957)
              ·
                refine ⟨145714627278418417689373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3108578715272926244039957 145714627278418417689373)
                ·
                  rfl

theorem cell21_1915503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 6].length) (baseStart_1915503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1915503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1915503 prefixEnd_1915503 := by exact prefixLift 1915503
  have htrace : WordTrace (prefixWord ++ tailWord_1915503) baseStart_1915503 baseEnd_1915503 := by
    simpa [prefixWord, tailWord_1915503, baseEnd_1915503] using wordTrace_append hprefix tailTrace_1915503
  have hstable : (prefixWord ++ tailWord_1915503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915503).length < 2 ^ (prefixWord ++ tailWord_1915503).sum := by decide
  have hdescent : baseEnd_1915503 < baseStart_1915503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915520 : List Nat := [2, 1, 1, 2, 1, 6, 3, 5]
def baseStart_1915520 : Nat := 118140960795 + 1915520 * 2 ^ 59
def prefixEnd_1915520 : Nat := 4983230072969 + 3 ^ 40 * 1915520 * 2
def baseEnd_1915520 : Nat := 145715920488955667094917

theorem tailTrace_1915520 : CollatzResearch.WordTrace tailWord_1915520 prefixEnd_1915520 145715920488955667094917 := by
  unfold tailWord_1915520
  simp only [CollatzResearch.WordTrace]
  refine ⟨34932377010202829807892007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46576502680270439743856009 34932377010202829807892007)
  ·
    refine ⟨52398565515304244711838011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34932377010202829807892007 52398565515304244711838011)
    ·
      refine ⟨78597848272956367067757017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52398565515304244711838011 78597848272956367067757017)
      ·
        refine ⟨58948386204717275300817763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78597848272956367067757017 58948386204717275300817763)
        ·
          refine ⟨88422579307075912951226645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58948386204717275300817763 88422579307075912951226645)
          ·
            refine ⟨4144808405019183419588749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 88422579307075912951226645 4144808405019183419588749)
            ·
              refine ⟨1554303151882193782345781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4144808405019183419588749 1554303151882193782345781)
              ·
                refine ⟨145715920488955667094917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1554303151882193782345781 145715920488955667094917)
                ·
                  rfl

theorem cell21_1915520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 5].length) (baseStart_1915520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1915520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1915520 prefixEnd_1915520 := by exact prefixLift 1915520
  have htrace : WordTrace (prefixWord ++ tailWord_1915520) baseStart_1915520 baseEnd_1915520 := by
    simpa [prefixWord, tailWord_1915520, baseEnd_1915520] using wordTrace_append hprefix tailTrace_1915520
  have hstable : (prefixWord ++ tailWord_1915520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915520).length < 2 ^ (prefixWord ++ tailWord_1915520).sum := by decide
  have hdescent : baseEnd_1915520 < baseStart_1915520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915534 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 7]
def baseStart_1915534 : Nat := 118140960795 + 1915534 * 2 ^ 59
def prefixEnd_1915534 : Nat := 4983230072969 + 3 ^ 40 * 1915534 * 2
def baseEnd_1915534 : Nat := 437150956457606088051389

theorem tailTrace_1915534 : CollatzResearch.WordTrace tailWord_1915534 prefixEnd_1915534 437150956457606088051389 := by
  unfold tailWord_1915534
  simp only [CollatzResearch.WordTrace]
  refine ⟨8733158080294367500849207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46576843094903293337862437 8733158080294367500849207)
  ·
    refine ⟨13099737120441551251273811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8733158080294367500849207 13099737120441551251273811)
    ·
      refine ⟨19649605680662326876910717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13099737120441551251273811 19649605680662326876910717)
      ·
        refine ⟨7368602130248372578841519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19649605680662326876910717 7368602130248372578841519)
        ·
          refine ⟨11052903195372558868262279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7368602130248372578841519 11052903195372558868262279)
          ·
            refine ⟨16579354793058838302393419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11052903195372558868262279 16579354793058838302393419)
            ·
              refine ⟨24869032189588257453590129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16579354793058838302393419 24869032189588257453590129)
              ·
                refine ⟨18651774142191193090192597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24869032189588257453590129 18651774142191193090192597)
                ·
                  refine ⟨437150956457606088051389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18651774142191193090192597 437150956457606088051389)
                  ·
                    rfl

theorem cell21_1915534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_1915534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1915534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1915534 prefixEnd_1915534 := by exact prefixLift 1915534
  have htrace : WordTrace (prefixWord ++ tailWord_1915534) baseStart_1915534 baseEnd_1915534 := by
    simpa [prefixWord, tailWord_1915534, baseEnd_1915534] using wordTrace_append hprefix tailTrace_1915534
  have hstable : (prefixWord ++ tailWord_1915534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915534).length < 2 ^ (prefixWord ++ tailWord_1915534).sum := by decide
  have hdescent : baseEnd_1915534 < baseStart_1915534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915596 : List Nat := [2, 2, 1, 5, 1, 3, 7]
def baseStart_1915596 : Nat := 118140960795 + 1915596 * 2 ^ 59
def prefixEnd_1915596 : Nat := 4983230072969 + 3 ^ 40 * 1915596 * 2
def baseEnd_1915596 : Nat := 48573900633589750890881

theorem tailTrace_1915596 : CollatzResearch.WordTrace tailWord_1915596 prefixEnd_1915596 48573900633589750890881 := by
  unfold tailWord_1915596
  simp only [CollatzResearch.WordTrace]
  refine ⟨34933762984065162297775321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46578350645420216397033761 34933762984065162297775321)
  ·
    refine ⟨26200322238048871723331491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34933762984065162297775321 26200322238048871723331491)
    ·
      refine ⟨39300483357073307584997237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26200322238048871723331491 39300483357073307584997237)
      ·
        refine ⟨3684420314725622586093491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39300483357073307584997237 3684420314725622586093491)
        ·
          refine ⟨5526630472088433879140237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3684420314725622586093491 5526630472088433879140237)
          ·
            refine ⟨2072486427033162704677589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5526630472088433879140237 2072486427033162704677589)
            ·
              refine ⟨48573900633589750890881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2072486427033162704677589 48573900633589750890881)
              ·
                rfl

theorem cell21_1915596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 7].length) (baseStart_1915596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1915596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1915596 prefixEnd_1915596 := by exact prefixLift 1915596
  have htrace : WordTrace (prefixWord ++ tailWord_1915596) baseStart_1915596 baseEnd_1915596 := by
    simpa [prefixWord, tailWord_1915596, baseEnd_1915596] using wordTrace_append hprefix tailTrace_1915596
  have hstable : (prefixWord ++ tailWord_1915596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915596).length < 2 ^ (prefixWord ++ tailWord_1915596).sum := by decide
  have hdescent : baseEnd_1915596 < baseStart_1915596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915655 : List Nat := [1, 1, 4, 4, 1, 10]
def baseStart_1915655 : Nat := 118140960795 + 1915655 * 2 ^ 59
def prefixEnd_1915655 : Nat := 4983230072969 + 3 ^ 40 * 1915655 * 2
def baseEnd_1915655 : Nat := 16191798900227287649425

theorem tailTrace_1915655 : CollatzResearch.WordTrace tailWord_1915655 prefixEnd_1915655 16191798900227287649425 := by
  unfold tailWord_1915655
  simp only [CollatzResearch.WordTrace]
  refine ⟨69869677874916577671948419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46579785249944385114632279 69869677874916577671948419)
  ·
    refine ⟨104804516812374866507922629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69869677874916577671948419 104804516812374866507922629)
    ·
      refine ⟨19650846902320287470235493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104804516812374866507922629 19650846902320287470235493)
      ·
        refine ⟨3684533794185053900669155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19650846902320287470235493 3684533794185053900669155)
        ·
          refine ⟨5526800691277580851003733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3684533794185053900669155 5526800691277580851003733)
          ·
            refine ⟨16191798900227287649425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5526800691277580851003733 16191798900227287649425)
            ·
              rfl

theorem cell21_1915655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 10].length) (baseStart_1915655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1915655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1915655 prefixEnd_1915655 := by exact prefixLift 1915655
  have htrace : WordTrace (prefixWord ++ tailWord_1915655) baseStart_1915655 baseEnd_1915655 := by
    simpa [prefixWord, tailWord_1915655, baseEnd_1915655] using wordTrace_append hprefix tailTrace_1915655
  have hstable : (prefixWord ++ tailWord_1915655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915655).length < 2 ^ (prefixWord ++ tailWord_1915655).sum := by decide
  have hdescent : baseEnd_1915655 < baseStart_1915655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915703 : List Nat := [1, 1, 3, 1, 2, 1, 6, 3, 3]
def baseStart_1915703 : Nat := 118140960795 + 1915703 * 2 ^ 59
def prefixEnd_1915703 : Nat := 4983230072969 + 3 ^ 40 * 1915703 * 2
def baseEnd_1915703 : Nat := 437189524560099349734377

theorem tailTrace_1915703 : CollatzResearch.WordTrace tailWord_1915703 prefixEnd_1915703 437189524560099349734377 := by
  unfold tailWord_1915703
  simp only [CollatzResearch.WordTrace]
  refine ⟨69871428578742681869695763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46580952385828454579797175 69871428578742681869695763)
  ·
    refine ⟨104807142868114022804543645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69871428578742681869695763 104807142868114022804543645)
    ·
      refine ⟨39302678575542758551703867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104807142868114022804543645 39302678575542758551703867)
      ·
        refine ⟨58954017863314137827555801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39302678575542758551703867 58954017863314137827555801)
        ·
          refine ⟨44215513397485603370666851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58954017863314137827555801 44215513397485603370666851)
          ·
            refine ⟨66323270096228405056000277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44215513397485603370666851 66323270096228405056000277)
            ·
              refine ⟨3108903285760706487000013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66323270096228405056000277 3108903285760706487000013)
              ·
                refine ⟨1165838732160264932625005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3108903285760706487000013 1165838732160264932625005)
                ·
                  refine ⟨437189524560099349734377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1165838732160264932625005 437189524560099349734377)
                  ·
                    rfl

theorem cell21_1915703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3, 3].length) (baseStart_1915703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1915703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1915703 prefixEnd_1915703 := by exact prefixLift 1915703
  have htrace : WordTrace (prefixWord ++ tailWord_1915703) baseStart_1915703 baseEnd_1915703 := by
    simpa [prefixWord, tailWord_1915703, baseEnd_1915703] using wordTrace_append hprefix tailTrace_1915703
  have hstable : (prefixWord ++ tailWord_1915703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915703).length < 2 ^ (prefixWord ++ tailWord_1915703).sum := by decide
  have hdescent : baseEnd_1915703 < baseStart_1915703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915745 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 7]
def baseStart_1915745 : Nat := 118140960795 + 1915745 * 2 ^ 59
def prefixEnd_1915745 : Nat := 4983230072969 + 3 ^ 40 * 1915745 * 2
def baseEnd_1915745 : Nat := 437199109532316610034291

theorem tailTrace_1915745 : CollatzResearch.WordTrace tailWord_1915745 prefixEnd_1915745 437199109532316610034291 := by
  unfold tailWord_1915745
  simp only [CollatzResearch.WordTrace]
  refine ⟨69872960444590523042724689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46581973629727015361816459 69872960444590523042724689)
  ·
    refine ⟨52404720333442892282043517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69872960444590523042724689 52404720333442892282043517)
    ·
      refine ⟨19651770125041084605766319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52404720333442892282043517 19651770125041084605766319)
      ·
        refine ⟨29477655187561626908649479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19651770125041084605766319 29477655187561626908649479)
        ·
          refine ⟨44216482781342440362974219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29477655187561626908649479 44216482781342440362974219)
          ·
            refine ⟨66324724172013660544461329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44216482781342440362974219 66324724172013660544461329)
            ·
              refine ⟨49743543129010245408345997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66324724172013660544461329 49743543129010245408345997)
              ·
                refine ⟨18653828673378842028129749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49743543129010245408345997 18653828673378842028129749)
                ·
                  refine ⟨437199109532316610034291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18653828673378842028129749 437199109532316610034291)
                  ·
                    rfl

theorem cell21_1915745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 7].length) (baseStart_1915745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1915745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1915745 prefixEnd_1915745 := by exact prefixLift 1915745
  have htrace : WordTrace (prefixWord ++ tailWord_1915745) baseStart_1915745 baseEnd_1915745 := by
    simpa [prefixWord, tailWord_1915745, baseEnd_1915745] using wordTrace_append hprefix tailTrace_1915745
  have hstable : (prefixWord ++ tailWord_1915745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915745).length < 2 ^ (prefixWord ++ tailWord_1915745).sum := by decide
  have hdescent : baseEnd_1915745 < baseStart_1915745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915748 : List Nat := [2, 3, 1, 1, 4, 1, 4, 5]
def baseStart_1915748 : Nat := 118140960795 + 1915748 * 2 ^ 59
def prefixEnd_1915748 : Nat := 4983230072969 + 3 ^ 40 * 1915748 * 2
def baseEnd_1915748 : Nat := 145733264724396423828095

theorem tailTrace_1915748 : CollatzResearch.WordTrace tailWord_1915748 prefixEnd_1915748 145733264724396423828095 := by
  unfold tailWord_1915748
  simp only [CollatzResearch.WordTrace]
  refine ⟨34936534931789827277541949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46582046575719769703389265 34936534931789827277541949)
  ·
    refine ⟨13101200599421185229078231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34936534931789827277541949 13101200599421185229078231)
    ·
      refine ⟨19651800899131777843617347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13101200599421185229078231 19651800899131777843617347)
      ·
        refine ⟨29477701348697666765426021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19651800899131777843617347 29477701348697666765426021)
        ·
          refine ⟨5527069002880812518517379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29477701348697666765426021 5527069002880812518517379)
          ·
            refine ⟨8290603504321218777776069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5527069002880812518517379 8290603504321218777776069)
            ·
              refine ⟨1554488157060228520833013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8290603504321218777776069 1554488157060228520833013)
              ·
                refine ⟨145733264724396423828095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1554488157060228520833013 145733264724396423828095)
                ·
                  rfl

theorem cell21_1915748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 5].length) (baseStart_1915748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1915748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1915748 prefixEnd_1915748 := by exact prefixLift 1915748
  have htrace : WordTrace (prefixWord ++ tailWord_1915748) baseStart_1915748 baseEnd_1915748 := by
    simpa [prefixWord, tailWord_1915748, baseEnd_1915748] using wordTrace_append hprefix tailTrace_1915748
  have hstable : (prefixWord ++ tailWord_1915748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915748).length < 2 ^ (prefixWord ++ tailWord_1915748).sum := by decide
  have hdescent : baseEnd_1915748 < baseStart_1915748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915807 : List Nat := [1, 1, 2, 5, 2, 1, 2, 7]
def baseStart_1915807 : Nat := 118140960795 + 1915807 * 2 ^ 59
def prefixEnd_1915807 : Nat := 4983230072969 + 3 ^ 40 * 1915807 * 2
def baseEnd_1915807 : Nat := 145737752925672760000277

theorem tailTrace_1915807 : CollatzResearch.WordTrace tailWord_1915807 prefixEnd_1915807 145737752925672760000277 := by
  unfold tailWord_1915807
  simp only [CollatzResearch.WordTrace]
  refine ⟨69875221770365907631481675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46583481180243938420987783 69875221770365907631481675)
  ·
    refine ⟨104812832655548861447222513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69875221770365907631481675 104812832655548861447222513)
    ·
      refine ⟨78609624491661646085416885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104812832655548861447222513 78609624491661646085416885)
      ·
        refine ⟨7369652296093279320507833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78609624491661646085416885 7369652296093279320507833)
        ·
          refine ⟨5527239222069959490380875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7369652296093279320507833 5527239222069959490380875)
          ·
            refine ⟨8290858833104939235571313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5527239222069959490380875 8290858833104939235571313)
            ·
              refine ⟨6218144124828704426678485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8290858833104939235571313 6218144124828704426678485)
              ·
                refine ⟨145737752925672760000277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6218144124828704426678485 145737752925672760000277)
                ·
                  rfl

theorem cell21_1915807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 7].length) (baseStart_1915807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1915807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1915807 prefixEnd_1915807 := by exact prefixLift 1915807
  have htrace : WordTrace (prefixWord ++ tailWord_1915807) baseStart_1915807 baseEnd_1915807 := by
    simpa [prefixWord, tailWord_1915807, baseEnd_1915807] using wordTrace_append hprefix tailTrace_1915807
  have hstable : (prefixWord ++ tailWord_1915807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915807).length < 2 ^ (prefixWord ++ tailWord_1915807).sum := by decide
  have hdescent : baseEnd_1915807 < baseStart_1915807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915838 : List Nat := [4, 2, 1, 1, 1, 2, 2, 3, 5]
def baseStart_1915838 : Nat := 118140960795 + 1915838 * 2 ^ 59
def prefixEnd_1915838 : Nat := 4983230072969 + 3 ^ 40 * 1915838 * 2
def baseEnd_1915838 : Nat := 437220333399369114984101

theorem tailTrace_1915838 : CollatzResearch.WordTrace tailWord_1915838 prefixEnd_1915838 437220333399369114984101 := by
  unfold tailWord_1915838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8734544054156699990732521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46584234955502399950573445 8734544054156699990732521)
  ·
    refine ⟨6550908040617524993049391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8734544054156699990732521 6550908040617524993049391)
    ·
      refine ⟨9826362060926287489574087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6550908040617524993049391 9826362060926287489574087)
      ·
        refine ⟨14739543091389431234361131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9826362060926287489574087 14739543091389431234361131)
        ·
          refine ⟨22109314637084146851541697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14739543091389431234361131 22109314637084146851541697)
          ·
            refine ⟨16581985977813110138656273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22109314637084146851541697 16581985977813110138656273)
            ·
              refine ⟨12436489483359832603992205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16581985977813110138656273 12436489483359832603992205)
              ·
                refine ⟨4663683556259937226497077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12436489483359832603992205 4663683556259937226497077)
                ·
                  refine ⟨437220333399369114984101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4663683556259937226497077 437220333399369114984101)
                  ·
                    rfl

theorem cell21_1915838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_1915838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1915838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1915838 prefixEnd_1915838 := by exact prefixLift 1915838
  have htrace : WordTrace (prefixWord ++ tailWord_1915838) baseStart_1915838 baseEnd_1915838 := by
    simpa [prefixWord, tailWord_1915838, baseEnd_1915838] using wordTrace_append hprefix tailTrace_1915838
  have hstable : (prefixWord ++ tailWord_1915838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915838).length < 2 ^ (prefixWord ++ tailWord_1915838).sum := by decide
  have hdescent : baseEnd_1915838 < baseStart_1915838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915914 : List Nat := [3, 1, 2, 2, 3, 1, 2, 2, 5]
def baseStart_1915914 : Nat := 118140960795 + 1915914 * 2 ^ 59
def prefixEnd_1915914 : Nat := 4983230072969 + 3 ^ 40 * 1915914 * 2
def baseEnd_1915914 : Nat := 437237677634809871717279

theorem tailTrace_1915914 : CollatzResearch.WordTrace tailWord_1915914 prefixEnd_1915914 437237677634809871717279 := by
  unfold tailWord_1915914
  simp only [CollatzResearch.WordTrace]
  refine ⟨17469781095244566226406699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46586082920652176603751197 17469781095244566226406699)
  ·
    refine ⟨26204671642866849339610049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17469781095244566226406699 26204671642866849339610049)
    ·
      refine ⟨19653503732150137004707537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26204671642866849339610049 19653503732150137004707537)
      ·
        refine ⟨14740127799112602753530653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19653503732150137004707537 14740127799112602753530653)
        ·
          refine ⟨5527547924667226032573995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14740127799112602753530653 5527547924667226032573995)
          ·
            refine ⟨8291321887000839048860993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5527547924667226032573995 8291321887000839048860993)
            ·
              refine ⟨6218491415250629286645745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8291321887000839048860993 6218491415250629286645745)
              ·
                refine ⟨4663868561437971964984309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6218491415250629286645745 4663868561437971964984309)
                ·
                  refine ⟨437237677634809871717279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4663868561437971964984309 437237677634809871717279)
                  ·
                    rfl

theorem cell21_1915914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_1915914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1915914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1915914 prefixEnd_1915914 := by exact prefixLift 1915914
  have htrace : WordTrace (prefixWord ++ tailWord_1915914) baseStart_1915914 baseEnd_1915914 := by
    simpa [prefixWord, tailWord_1915914, baseEnd_1915914] using wordTrace_append hprefix tailTrace_1915914
  have hstable : (prefixWord ++ tailWord_1915914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915914).length < 2 ^ (prefixWord ++ tailWord_1915914).sum := by decide
  have hdescent : baseEnd_1915914 < baseStart_1915914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915928 : List Nat := [2, 1, 2, 3, 2, 2, 1, 2, 6]
def baseStart_1915928 : Nat := 118140960795 + 1915928 * 2 ^ 59
def prefixEnd_1915928 : Nat := 4983230072969 + 3 ^ 40 * 1915928 * 2
def baseEnd_1915928 : Nat := 437240872625548958483917

theorem tailTrace_1915928 : CollatzResearch.WordTrace tailWord_1915928 prefixEnd_1915928 437240872625548958483917 := by
  unfold tailWord_1915928
  simp only [CollatzResearch.WordTrace]
  refine ⟨34939817501463772648318219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46586423335285030197757625 34939817501463772648318219)
  ·
    refine ⟨52409726252195658972477329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34939817501463772648318219 52409726252195658972477329)
    ·
      refine ⟨39307294689146744229357997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52409726252195658972477329 39307294689146744229357997)
      ·
        refine ⟨14740235508430029086009249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39307294689146744229357997 14740235508430029086009249)
        ·
          refine ⟨11055176631322521814506937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14740235508430029086009249 11055176631322521814506937)
          ·
            refine ⟨8291382473491891360880203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11055176631322521814506937 8291382473491891360880203)
            ·
              refine ⟨12437073710237837041320305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8291382473491891360880203 12437073710237837041320305)
              ·
                refine ⟨9327805282678377780990229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12437073710237837041320305 9327805282678377780990229)
                ·
                  refine ⟨437240872625548958483917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9327805282678377780990229 437240872625548958483917)
                  ·
                    rfl

theorem cell21_1915928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 6].length) (baseStart_1915928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1915928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1915928 prefixEnd_1915928 := by exact prefixLift 1915928
  have htrace : WordTrace (prefixWord ++ tailWord_1915928) baseStart_1915928 baseEnd_1915928 := by
    simpa [prefixWord, tailWord_1915928, baseEnd_1915928] using wordTrace_append hprefix tailTrace_1915928
  have hstable : (prefixWord ++ tailWord_1915928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915928).length < 2 ^ (prefixWord ++ tailWord_1915928).sum := by decide
  have hdescent : baseEnd_1915928 < baseStart_1915928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915973 : List Nat := [1, 3, 1, 1, 1, 3, 2, 4, 5]
def baseStart_1915973 : Nat := 118140960795 + 1915973 * 2 ^ 59
def prefixEnd_1915973 : Nat := 4983230072969 + 3 ^ 40 * 1915973 * 2
def baseEnd_1915973 : Nat := 437251142238638880233825

theorem tailTrace_1915973 : CollatzResearch.WordTrace tailWord_1915973 prefixEnd_1915973 437251142238638880233825 := by
  unfold tailWord_1915973
  simp only [CollatzResearch.WordTrace]
  refine ⟨69881276287764517982024573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46587517525176345321349715 69881276287764517982024573)
  ·
    refine ⟨26205478607911694243259215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69881276287764517982024573 26205478607911694243259215)
    ·
      refine ⟨39308217911867541364888823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26205478607911694243259215 39308217911867541364888823)
      ·
        refine ⟨58962326867801312047333235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39308217911867541364888823 58962326867801312047333235)
        ·
          refine ⟨88443490301701968070999853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58962326867801312047333235 88443490301701968070999853)
          ·
            refine ⟨33166308863138238026624945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88443490301701968070999853 33166308863138238026624945)
            ·
              refine ⟨24874731647353678519968709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33166308863138238026624945 24874731647353678519968709)
              ·
                refine ⟨4664012183878814722494133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24874731647353678519968709 4664012183878814722494133)
                ·
                  refine ⟨437251142238638880233825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4664012183878814722494133 437251142238638880233825)
                  ·
                    rfl

theorem cell21_1915973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_1915973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1915973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1915973 prefixEnd_1915973 := by exact prefixLift 1915973
  have htrace : WordTrace (prefixWord ++ tailWord_1915973) baseStart_1915973 baseEnd_1915973 := by
    simpa [prefixWord, tailWord_1915973, baseEnd_1915973] using wordTrace_append hprefix tailTrace_1915973
  have hstable : (prefixWord ++ tailWord_1915973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915973).length < 2 ^ (prefixWord ++ tailWord_1915973).sum := by decide
  have hdescent : baseEnd_1915973 < baseStart_1915973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916007 : List Nat := [1, 1, 5, 1, 1, 4, 1, 4, 3]
def baseStart_1916007 : Nat := 118140960795 + 1916007 * 2 ^ 59
def prefixEnd_1916007 : Nat := 4983230072969 + 3 ^ 40 * 1916007 * 2
def baseEnd_1916007 : Nat := 437258901501862376667089

theorem tailTrace_1916007 : CollatzResearch.WordTrace tailWord_1916007 prefixEnd_1916007 437258901501862376667089 := by
  unfold tailWord_1916007
  simp only [CollatzResearch.WordTrace]
  refine ⟨69882516369641341788762275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46588344246427561192508183 69882516369641341788762275)
  ·
    refine ⟨104823774554462012683143413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69882516369641341788762275 104823774554462012683143413)
    ·
      refine ⟨9827228864480813689044695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104823774554462012683143413 9827228864480813689044695)
      ·
        refine ⟨14740843296721220533567043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9827228864480813689044695 14740843296721220533567043)
        ·
          refine ⟨22111264945081830800350565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14740843296721220533567043 22111264945081830800350565)
          ·
            refine ⟨4145862177202843275065731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22111264945081830800350565 4145862177202843275065731)
            ·
              refine ⟨6218793265804264912598597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4145862177202843275065731 6218793265804264912598597)
              ·
                refine ⟨1166023737338299671112237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6218793265804264912598597 1166023737338299671112237)
                ·
                  refine ⟨437258901501862376667089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1166023737338299671112237 437258901501862376667089)
                  ·
                    rfl

theorem cell21_1916007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4, 3].length) (baseStart_1916007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1916007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1916007 prefixEnd_1916007 := by exact prefixLift 1916007
  have htrace : WordTrace (prefixWord ++ tailWord_1916007) baseStart_1916007 baseEnd_1916007 := by
    simpa [prefixWord, tailWord_1916007, baseEnd_1916007] using wordTrace_append hprefix tailTrace_1916007
  have hstable : (prefixWord ++ tailWord_1916007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916007).length < 2 ^ (prefixWord ++ tailWord_1916007).sum := by decide
  have hdescent : baseEnd_1916007 < baseStart_1916007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916035 : List Nat := [1, 1, 1, 3, 3, 2, 5, 5]
def baseStart_1916035 : Nat := 118140960795 + 1916035 * 2 ^ 59
def prefixEnd_1916035 : Nat := 4983230072969 + 3 ^ 40 * 1916035 * 2
def baseEnd_1916035 : Nat := 145755097161113516733455

theorem tailTrace_1916035 : CollatzResearch.WordTrace tailWord_1916035 prefixEnd_1916035 145755097161113516733455 := by
  unfold tailWord_1916035
  simp only [CollatzResearch.WordTrace]
  refine ⟨69883537613539902570781559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46589025075693268380521039 69883537613539902570781559)
  ·
    refine ⟨104825306420309853856172339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69883537613539902570781559 104825306420309853856172339)
    ·
      refine ⟨157237959630464780784258509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104825306420309853856172339 157237959630464780784258509)
      ·
        refine ⟨58964234861424292794096941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157237959630464780784258509 58964234861424292794096941)
        ·
          refine ⟨22111588073034109797786353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58964234861424292794096941 22111588073034109797786353)
          ·
            refine ⟨16583691054775582348339765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22111588073034109797786353 16583691054775582348339765)
            ·
              refine ⟨1554721036385210845156853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16583691054775582348339765 1554721036385210845156853)
              ·
                refine ⟨145755097161113516733455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1554721036385210845156853 145755097161113516733455)
                ·
                  rfl

theorem cell21_1916035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 5].length) (baseStart_1916035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1916035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1916035 prefixEnd_1916035 := by exact prefixLift 1916035
  have htrace : WordTrace (prefixWord ++ tailWord_1916035) baseStart_1916035 baseEnd_1916035 := by
    simpa [prefixWord, tailWord_1916035, baseEnd_1916035] using wordTrace_append hprefix tailTrace_1916035
  have hstable : (prefixWord ++ tailWord_1916035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916035).length < 2 ^ (prefixWord ++ tailWord_1916035).sum := by decide
  have hdescent : baseEnd_1916035 < baseStart_1916035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916097 : List Nat := [1, 2, 6, 1, 1, 1, 1, 2, 6]
def baseStart_1916097 : Nat := 118140960795 + 1916097 * 2 ^ 59
def prefixEnd_1916097 : Nat := 4983230072969 + 3 ^ 40 * 1916097 * 2
def baseEnd_1916097 : Nat := 437279440728042220166905

theorem tailTrace_1916097 : CollatzResearch.WordTrace tailWord_1916097 prefixEnd_1916097 437279440728042220166905 := by
  unfold tailWord_1916097
  simp only [CollatzResearch.WordTrace]
  refine ⟨69885798939315287159538545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46590532626210191439692363 69885798939315287159538545)
  ·
    refine ⟨52414349204486465369653909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69885798939315287159538545 52414349204486465369653909)
    ·
      refine ⟨2456922618960303064202527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52414349204486465369653909 2456922618960303064202527)
      ·
        refine ⟨3685383928440454596303791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2456922618960303064202527 3685383928440454596303791)
        ·
          refine ⟨5528075892660681894455687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3685383928440454596303791 5528075892660681894455687)
          ·
            refine ⟨8292113838991022841683531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5528075892660681894455687 8292113838991022841683531)
            ·
              refine ⟨12438170758486534262525297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8292113838991022841683531 12438170758486534262525297)
              ·
                refine ⟨9328628068864900696893973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12438170758486534262525297 9328628068864900696893973)
                ·
                  refine ⟨437279440728042220166905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9328628068864900696893973 437279440728042220166905)
                  ·
                    rfl

theorem cell21_1916097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 6].length) (baseStart_1916097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1916097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1916097 prefixEnd_1916097 := by exact prefixLift 1916097
  have htrace : WordTrace (prefixWord ++ tailWord_1916097) baseStart_1916097 baseEnd_1916097 := by
    simpa [prefixWord, tailWord_1916097, baseEnd_1916097] using wordTrace_append hprefix tailTrace_1916097
  have hstable : (prefixWord ++ tailWord_1916097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916097).length < 2 ^ (prefixWord ++ tailWord_1916097).sum := by decide
  have hdescent : baseEnd_1916097 < baseStart_1916097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916263 : List Nat := [1, 1, 5, 1, 4, 1, 1, 7]
def baseStart_1916263 : Nat := 118140960795 + 1916263 * 2 ^ 59
def prefixEnd_1916263 : Nat := 4983230072969 + 3 ^ 40 * 1916263 * 2
def baseEnd_1916263 : Nat := 145772441396554273466633

theorem tailTrace_1916263 : CollatzResearch.WordTrace tailWord_1916263 prefixEnd_1916263 145772441396554273466633 := by
  unfold tailWord_1916263
  simp only [CollatzResearch.WordTrace]
  refine ⟨69891853456713897510081443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46594568971142598340054295 69891853456713897510081443)
  ·
    refine ⟨104837780185070846265122165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69891853456713897510081443 104837780185070846265122165)
    ·
      refine ⟨9828541892350391837355203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104837780185070846265122165 9828541892350391837355203)
      ·
        refine ⟨14742812838525587756032805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9828541892350391837355203 14742812838525587756032805)
        ·
          refine ⟨2764277407223547704256151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14742812838525587756032805 2764277407223547704256151)
          ·
            refine ⟨4146416110835321556384227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2764277407223547704256151 4146416110835321556384227)
            ·
              refine ⟨6219624166252982334576341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4146416110835321556384227 6219624166252982334576341)
              ·
                refine ⟨145772441396554273466633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6219624166252982334576341 145772441396554273466633)
                ·
                  rfl

theorem cell21_1916263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 7].length) (baseStart_1916263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1916263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1916263 prefixEnd_1916263 := by exact prefixLift 1916263
  have htrace : WordTrace (prefixWord ++ tailWord_1916263) baseStart_1916263 baseEnd_1916263 := by
    simpa [prefixWord, tailWord_1916263, baseEnd_1916263] using wordTrace_append hprefix tailTrace_1916263
  have hstable : (prefixWord ++ tailWord_1916263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916263).length < 2 ^ (prefixWord ++ tailWord_1916263).sum := by decide
  have hdescent : baseEnd_1916263 < baseStart_1916263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916286 : List Nat := [4, 2, 3, 2, 1, 1, 3, 2, 3]
def baseStart_1916286 : Nat := 118140960795 + 1916286 * 2 ^ 59
def prefixEnd_1916286 : Nat := 4983230072969 + 3 ^ 40 * 1916286 * 2
def baseEnd_1916286 : Nat := 437322573103019891516519

theorem tailTrace_1916286 : CollatzResearch.WordTrace tailWord_1916286 prefixEnd_1916286 437322573103019891516519 := by
  unfold tailWord_1916286
  simp only [CollatzResearch.WordTrace]
  refine ⟨8736586541953821554771089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46595128223753714958779141 8736586541953821554771089)
  ·
    refine ⟨6552439906465366166078317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8736586541953821554771089 6552439906465366166078317)
    ·
      refine ⟨2457164964924512312279369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6552439906465366166078317 2457164964924512312279369)
      ·
        refine ⟨1842873723693384234209527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2457164964924512312279369 1842873723693384234209527)
        ·
          refine ⟨2764310585540076351314291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1842873723693384234209527 2764310585540076351314291)
          ·
            refine ⟨4146465878310114526971437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2764310585540076351314291 4146465878310114526971437)
            ·
              refine ⟨1554924704366292947614289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4146465878310114526971437 1554924704366292947614289)
              ·
                refine ⟨1166193528274719710710717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1554924704366292947614289 1166193528274719710710717)
                ·
                  refine ⟨437322573103019891516519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1166193528274719710710717 437322573103019891516519)
                  ·
                    rfl

theorem cell21_1916286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_1916286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1916286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1916286 prefixEnd_1916286 := by exact prefixLift 1916286
  have htrace : WordTrace (prefixWord ++ tailWord_1916286) baseStart_1916286 baseEnd_1916286 := by
    simpa [prefixWord, tailWord_1916286, baseEnd_1916286] using wordTrace_append hprefix tailTrace_1916286
  have hstable : (prefixWord ++ tailWord_1916286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916286).length < 2 ^ (prefixWord ++ tailWord_1916286).sum := by decide
  have hdescent : baseEnd_1916286 < baseStart_1916286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916336 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 9]
def baseStart_1916336 : Nat := 118140960795 + 1916336 * 2 ^ 59
def prefixEnd_1916336 : Nat := 4983230072969 + 3 ^ 40 * 1916336 * 2
def baseEnd_1916336 : Nat := 437333983784230915683083

theorem tailTrace_1916336 : CollatzResearch.WordTrace tailWord_1916336 prefixEnd_1916336 437333983784230915683083 := by
  unfold tailWord_1916336
  simp only [CollatzResearch.WordTrace]
  refine ⟨34947257992724715488744431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46596343990299620651659241 34947257992724715488744431)
  ·
    refine ⟨52420886989087073233116647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34947257992724715488744431 52420886989087073233116647)
    ·
      refine ⟨78631330483630609849674971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52420886989087073233116647 78631330483630609849674971)
      ·
        refine ⟨117946995725445914774512457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78631330483630609849674971 117946995725445914774512457)
        ·
          refine ⟨88460246794084436080884343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117946995725445914774512457 88460246794084436080884343)
          ·
            refine ⟨132690370191126654121326515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88460246794084436080884343 132690370191126654121326515)
            ·
              refine ⟨199035555286689981181989773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132690370191126654121326515 199035555286689981181989773)
              ·
                refine ⟨74638333232508742943246165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199035555286689981181989773 74638333232508742943246165)
                ·
                  refine ⟨437333983784230915683083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74638333232508742943246165 437333983784230915683083)
                  ·
                    rfl

theorem cell21_1916336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 9].length) (baseStart_1916336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1916336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1916336 prefixEnd_1916336 := by exact prefixLift 1916336
  have htrace : WordTrace (prefixWord ++ tailWord_1916336) baseStart_1916336 baseEnd_1916336 := by
    simpa [prefixWord, tailWord_1916336, baseEnd_1916336] using wordTrace_append hprefix tailTrace_1916336
  have hstable : (prefixWord ++ tailWord_1916336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916336).length < 2 ^ (prefixWord ++ tailWord_1916336).sum := by decide
  have hdescent : baseEnd_1916336 < baseStart_1916336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916345 : List Nat := [1, 2, 1, 4, 5, 1, 2, 2, 3]
def baseStart_1916345 : Nat := 118140960795 + 1916345 * 2 ^ 59
def prefixEnd_1916345 : Nat := 4983230072969 + 3 ^ 40 * 1916345 * 2
def baseEnd_1916345 : Nat := 437336037706848900033065

theorem tailTrace_1916345 : CollatzResearch.WordTrace tailWord_1916345 prefixEnd_1916345 437336037706848900033065 := by
  unfold tailWord_1916345
  simp only [CollatzResearch.WordTrace]
  refine ⟨69894844242416825514566489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46596562828277883676377659 69894844242416825514566489)
  ·
    refine ⟨52421133181812619135924867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69894844242416825514566489 52421133181812619135924867)
    ·
      refine ⟨78631699772718928703887301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52421133181812619135924867 78631699772718928703887301)
      ·
        refine ⟨14743443707384799131978869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78631699772718928703887301 14743443707384799131978869)
        ·
          refine ⟨1382197847567324918623019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14743443707384799131978869 1382197847567324918623019)
          ·
            refine ⟨2073296771350987377934529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1382197847567324918623019 2073296771350987377934529)
            ·
              refine ⟨1554972578513240533450897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2073296771350987377934529 1554972578513240533450897)
              ·
                refine ⟨1166229433884930400088173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1554972578513240533450897 1166229433884930400088173)
                ·
                  refine ⟨437336037706848900033065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1166229433884930400088173 437336037706848900033065)
                  ·
                    rfl

theorem cell21_1916345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2, 3].length) (baseStart_1916345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1916345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1916345 prefixEnd_1916345 := by exact prefixLift 1916345
  have htrace : WordTrace (prefixWord ++ tailWord_1916345) baseStart_1916345 baseEnd_1916345 := by
    simpa [prefixWord, tailWord_1916345, baseEnd_1916345] using wordTrace_append hprefix tailTrace_1916345
  have hstable : (prefixWord ++ tailWord_1916345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916345).length < 2 ^ (prefixWord ++ tailWord_1916345).sum := by decide
  have hdescent : baseEnd_1916345 < baseStart_1916345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916356 : List Nat := [2, 3, 3, 2, 1, 3, 1, 6]
def baseStart_1916356 : Nat := 118140960795 + 1916356 * 2 ^ 59
def prefixEnd_1916356 : Nat := 4983230072969 + 3 ^ 40 * 1916356 * 2
def baseEnd_1916356 : Nat := 145779516018905108449903

theorem tailTrace_1916356 : CollatzResearch.WordTrace tailWord_1916356 prefixEnd_1916356 145779516018905108449903 := by
  unfold tailWord_1916356
  simp only [CollatzResearch.WordTrace]
  refine ⟨34947622722688487196608461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46596830296917982928811281 34947622722688487196608461)
  ·
    refine ⟨13105358521008182698728173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34947622722688487196608461 13105358521008182698728173)
    ·
      refine ⟨4914509445378068512023065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13105358521008182698728173 4914509445378068512023065)
      ·
        refine ⟨3685882084033551384017299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4914509445378068512023065 3685882084033551384017299)
        ·
          refine ⟨5528823126050327076025949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3685882084033551384017299 5528823126050327076025949)
          ·
            refine ⟨2073308672268872653509731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5528823126050327076025949 2073308672268872653509731)
            ·
              refine ⟨3109963008403308980264597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2073308672268872653509731 3109963008403308980264597)
              ·
                refine ⟨145779516018905108449903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3109963008403308980264597 145779516018905108449903)
                ·
                  rfl

theorem cell21_1916356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 6].length) (baseStart_1916356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1916356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1916356 prefixEnd_1916356 := by exact prefixLift 1916356
  have htrace : WordTrace (prefixWord ++ tailWord_1916356) baseStart_1916356 baseEnd_1916356 := by
    simpa [prefixWord, tailWord_1916356, baseEnd_1916356] using wordTrace_append hprefix tailTrace_1916356
  have hstable : (prefixWord ++ tailWord_1916356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916356).length < 2 ^ (prefixWord ++ tailWord_1916356).sum := by decide
  have hdescent : baseEnd_1916356 < baseStart_1916356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916387 : List Nat := [1, 1, 1, 6, 2, 2, 2, 3, 3]
def baseStart_1916387 : Nat := 118140960795 + 1916387 * 2 ^ 59
def prefixEnd_1916387 : Nat := 4983230072969 + 3 ^ 40 * 1916387 * 2
def baseEnd_1916387 : Nat := 437345622679066160332979

theorem tailTrace_1916387 : CollatzResearch.WordTrace tailWord_1916387 prefixEnd_1916387 437345622679066160332979 := by
  unfold tailWord_1916387
  simp only [CollatzResearch.WordTrace]
  refine ⟨69896376108264666687595415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46597584072176444458396943 69896376108264666687595415)
  ·
    refine ⟨104844564162397000031393123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69896376108264666687595415 104844564162397000031393123)
    ·
      refine ⟨157266846243595500047089685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104844564162397000031393123 157266846243595500047089685)
      ·
        refine ⟨7371883417668539064707329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 157266846243595500047089685 7371883417668539064707329)
        ·
          refine ⟨5528912563251404298530497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7371883417668539064707329 5528912563251404298530497)
          ·
            refine ⟨4146684422438553223897873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5528912563251404298530497 4146684422438553223897873)
            ·
              refine ⟨3110013316828914917923405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4146684422438553223897873 3110013316828914917923405)
              ·
                refine ⟨1166254993810843094221277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3110013316828914917923405 1166254993810843094221277)
                ·
                  refine ⟨437345622679066160332979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1166254993810843094221277 437345622679066160332979)
                  ·
                    rfl

theorem cell21_1916387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3, 3].length) (baseStart_1916387 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1916387 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1916387 prefixEnd_1916387 := by exact prefixLift 1916387
  have htrace : WordTrace (prefixWord ++ tailWord_1916387) baseStart_1916387 baseEnd_1916387 := by
    simpa [prefixWord, tailWord_1916387, baseEnd_1916387] using wordTrace_append hprefix tailTrace_1916387
  have hstable : (prefixWord ++ tailWord_1916387).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916387).length < 2 ^ (prefixWord ++ tailWord_1916387).sum := by decide
  have hdescent : baseEnd_1916387 < baseStart_1916387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916398 : List Nat := [4, 1, 2, 1, 2, 1, 10]
def baseStart_1916398 : Nat := 118140960795 + 1916398 * 2 ^ 59
def prefixEnd_1916398 : Nat := 4983230072969 + 3 ^ 40 * 1916398 * 2
def baseEnd_1916398 : Nat := 48594237003214731738847

theorem tailTrace_1916398 : CollatzResearch.WordTrace tailWord_1916398 prefixEnd_1916398 48594237003214731738847 := by
  unfold tailWord_1916398
  simp only [CollatzResearch.WordTrace]
  refine ⟨8737097163903101945780731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46597851540816543710830565 8737097163903101945780731)
  ·
    refine ⟨13105645745854652918671097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8737097163903101945780731 13105645745854652918671097)
    ·
      refine ⟨9829234309390989689003323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13105645745854652918671097 9829234309390989689003323)
      ·
        refine ⟨14743851464086484533504985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9829234309390989689003323 14743851464086484533504985)
        ·
          refine ⟨11057888598064863400128739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14743851464086484533504985 11057888598064863400128739)
          ·
            refine ⟨16586832897097295100193109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11057888598064863400128739 16586832897097295100193109)
            ·
              refine ⟨48594237003214731738847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16586832897097295100193109 48594237003214731738847)
              ·
                rfl

theorem cell21_1916398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 10].length) (baseStart_1916398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1916398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1916398 prefixEnd_1916398 := by exact prefixLift 1916398
  have htrace : WordTrace (prefixWord ++ tailWord_1916398) baseStart_1916398 baseEnd_1916398 := by
    simpa [prefixWord, tailWord_1916398, baseEnd_1916398] using wordTrace_append hprefix tailTrace_1916398
  have hstable : (prefixWord ++ tailWord_1916398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916398).length < 2 ^ (prefixWord ++ tailWord_1916398).sum := by decide
  have hdescent : baseEnd_1916398 < baseStart_1916398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916401 : List Nat := [1, 2, 2, 2, 3, 4, 1, 2, 4]
def baseStart_1916401 : Nat := 118140960795 + 1916401 * 2 ^ 59
def prefixEnd_1916401 : Nat := 4983230072969 + 3 ^ 40 * 1916401 * 2
def baseEnd_1916401 : Nat := 437348817669805247099617

theorem tailTrace_1916401 : CollatzResearch.WordTrace tailWord_1916401 prefixEnd_1916401 437348817669805247099617 := by
  unfold tailWord_1916401
  simp only [CollatzResearch.WordTrace]
  refine ⟨69896886730213947078605057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46597924486809298052403371 69896886730213947078605057)
  ·
    refine ⟨52422665047660460308953793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69896886730213947078605057 52422665047660460308953793)
    ·
      refine ⟨39316998785745345231715345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52422665047660460308953793 39316998785745345231715345)
      ·
        refine ⟨29487749089309008923786509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39316998785745345231715345 29487749089309008923786509)
        ·
          refine ⟨11057905908490878346419941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29487749089309008923786509 11057905908490878346419941)
          ·
            refine ⟨2073357357842039689953739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11057905908490878346419941 2073357357842039689953739)
            ·
              refine ⟨3110036036763059534930609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2073357357842039689953739 3110036036763059534930609)
              ·
                refine ⟨2332527027572294651197957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3110036036763059534930609 2332527027572294651197957)
                ·
                  refine ⟨437348817669805247099617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2332527027572294651197957 437348817669805247099617)
                  ·
                    rfl

theorem cell21_1916401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 4].length) (baseStart_1916401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1916401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1916401 prefixEnd_1916401 := by exact prefixLift 1916401
  have htrace : WordTrace (prefixWord ++ tailWord_1916401) baseStart_1916401 baseEnd_1916401 := by
    simpa [prefixWord, tailWord_1916401, baseEnd_1916401] using wordTrace_append hprefix tailTrace_1916401
  have hstable : (prefixWord ++ tailWord_1916401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916401).length < 2 ^ (prefixWord ++ tailWord_1916401).sum := by decide
  have hdescent : baseEnd_1916401 < baseStart_1916401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916474 : List Nat := [3, 1, 1, 1, 3, 2, 4, 6]
def baseStart_1916474 : Nat := 118140960795 + 1916474 * 2 ^ 59
def prefixEnd_1916474 : Nat := 4983230072969 + 3 ^ 40 * 1916474 * 2
def baseEnd_1916474 : Nat := 145788492421457780794267

theorem tailTrace_1916474 : CollatzResearch.WordTrace tailWord_1916474 prefixEnd_1916474 145788492421457780794267 := by
  unfold tailWord_1916474
  simp only [CollatzResearch.WordTrace]
  refine ⟨17474887314737370136503119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46599699505966320364008317 17474887314737370136503119)
  ·
    refine ⟨26212330972106055204754679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17474887314737370136503119 26212330972106055204754679)
    ·
      refine ⟨39318496458159082807132019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26212330972106055204754679 39318496458159082807132019)
      ·
        refine ⟨58977744687238624210698029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39318496458159082807132019 58977744687238624210698029)
        ·
          refine ⟨22116654257714484079011761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58977744687238624210698029 22116654257714484079011761)
          ·
            refine ⟨16587490693285863059258821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22116654257714484079011761 16587490693285863059258821)
            ·
              refine ⟨3110154504991099323611029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16587490693285863059258821 3110154504991099323611029)
              ·
                refine ⟨145788492421457780794267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3110154504991099323611029 145788492421457780794267)
                ·
                  rfl

theorem cell21_1916474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 6].length) (baseStart_1916474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1916474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1916474 prefixEnd_1916474 := by exact prefixLift 1916474
  have htrace : WordTrace (prefixWord ++ tailWord_1916474) baseStart_1916474 baseEnd_1916474 := by
    simpa [prefixWord, tailWord_1916474, baseEnd_1916474] using wordTrace_append hprefix tailTrace_1916474
  have hstable : (prefixWord ++ tailWord_1916474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916474).length < 2 ^ (prefixWord ++ tailWord_1916474).sum := by decide
  have hdescent : baseEnd_1916474 < baseStart_1916474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916477 : List Nat := [1, 4, 1, 3, 3, 1, 1, 3, 4]
def baseStart_1916477 : Nat := 118140960795 + 1916477 * 2 ^ 59
def prefixEnd_1916477 : Nat := 4983230072969 + 3 ^ 40 * 1916477 * 2
def baseEnd_1916477 : Nat := 437366161905246003832795

theorem tailTrace_1916477 : CollatzResearch.WordTrace tailWord_1916477 prefixEnd_1916477 437366161905246003832795 := by
  unfold tailWord_1916477
  simp only [CollatzResearch.WordTrace]
  refine ⟨69899658677938612058371685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46599772451959074705581123 69899658677938612058371685)
  ·
    refine ⟨13106186002113489760944691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69899658677938612058371685 13106186002113489760944691)
    ·
      refine ⟨19659279003170234641417037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13106186002113489760944691 19659279003170234641417037)
      ·
        refine ⟨7372229626188837990531389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19659279003170234641417037 7372229626188837990531389)
        ·
          refine ⟨2764586109820814246449271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7372229626188837990531389 2764586109820814246449271)
          ·
            refine ⟨4146879164731221369673907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2764586109820814246449271 4146879164731221369673907)
            ·
              refine ⟨6220318747096832054510861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4146879164731221369673907 6220318747096832054510861)
              ·
                refine ⟨2332619530161312020441573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6220318747096832054510861 2332619530161312020441573)
                ·
                  refine ⟨437366161905246003832795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2332619530161312020441573 437366161905246003832795)
                  ·
                    rfl

theorem cell21_1916477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_1916477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1916477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1916477 prefixEnd_1916477 := by exact prefixLift 1916477
  have htrace : WordTrace (prefixWord ++ tailWord_1916477) baseStart_1916477 baseEnd_1916477 := by
    simpa [prefixWord, tailWord_1916477, baseEnd_1916477] using wordTrace_append hprefix tailTrace_1916477
  have hstable : (prefixWord ++ tailWord_1916477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916477).length < 2 ^ (prefixWord ++ tailWord_1916477).sum := by decide
  have hdescent : baseEnd_1916477 < baseStart_1916477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916519 : List Nat := [1, 1, 5, 1, 1, 1, 2, 3, 6]
def baseStart_1916519 : Nat := 118140960795 + 1916519 * 2 ^ 59
def prefixEnd_1916519 : Nat := 4983230072969 + 3 ^ 40 * 1916519 * 2
def baseEnd_1916519 : Nat := 437375746877463264132709

theorem tailTrace_1916519 : CollatzResearch.WordTrace tailWord_1916519 prefixEnd_1916519 437375746877463264132709 := by
  unfold tailWord_1916519
  simp only [CollatzResearch.WordTrace]
  refine ⟨69901190543786453231400611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46600793695857635487600407 69901190543786453231400611)
  ·
    refine ⟨104851785815679679847100917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69901190543786453231400611 104851785815679679847100917)
    ·
      refine ⟨9829854920219969985665711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104851785815679679847100917 9829854920219969985665711)
      ·
        refine ⟨14744782380329954978498567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9829854920219969985665711 14744782380329954978498567)
        ·
          refine ⟨22117173570494932467747851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14744782380329954978498567 22117173570494932467747851)
          ·
            refine ⟨33175760355742398701621777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22117173570494932467747851 33175760355742398701621777)
            ·
              refine ⟨24881820266806799026216333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33175760355742398701621777 24881820266806799026216333)
              ·
                refine ⟨9330682600052549634831125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24881820266806799026216333 9330682600052549634831125)
                ·
                  refine ⟨437375746877463264132709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9330682600052549634831125 437375746877463264132709)
                  ·
                    rfl

theorem cell21_1916519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 6].length) (baseStart_1916519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1916519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1916519 prefixEnd_1916519 := by exact prefixLift 1916519
  have htrace : WordTrace (prefixWord ++ tailWord_1916519) baseStart_1916519 baseEnd_1916519 := by
    simpa [prefixWord, tailWord_1916519, baseEnd_1916519] using wordTrace_append hprefix tailTrace_1916519
  have hstable : (prefixWord ++ tailWord_1916519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916519).length < 2 ^ (prefixWord ++ tailWord_1916519).sum := by decide
  have hdescent : baseEnd_1916519 < baseStart_1916519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916626 : List Nat := [3, 2, 2, 2, 2, 1, 9]
def baseStart_1916626 : Nat := 118140960795 + 1916626 * 2 ^ 59
def prefixEnd_1916626 : Nat := 4983230072969 + 3 ^ 40 * 1916626 * 2
def baseEnd_1916626 : Nat := 48600018415028317316573

theorem tailTrace_1916626 : CollatzResearch.WordTrace tailWord_1916626 prefixEnd_1916626 48600018415028317316573 := by
  unfold tailWord_1916626
  simp only [CollatzResearch.WordTrace]
  refine ⟨17476273288599702626386433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46603395436265873670363821 17476273288599702626386433)
  ·
    refine ⟨13107204966449776969789825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17476273288599702626386433 13107204966449776969789825)
    ·
      refine ⟨9830403724837332727342369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13107204966449776969789825 9830403724837332727342369)
      ·
        refine ⟨7372802793627999545506777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9830403724837332727342369 7372802793627999545506777)
        ·
          refine ⟨5529602095220999659130083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7372802793627999545506777 5529602095220999659130083)
          ·
            refine ⟨8294403142831499488695125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5529602095220999659130083 8294403142831499488695125)
            ·
              refine ⟨48600018415028317316573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8294403142831499488695125 48600018415028317316573)
              ·
                rfl

theorem cell21_1916626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 9].length) (baseStart_1916626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1916626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1916626 prefixEnd_1916626 := by exact prefixLift 1916626
  have htrace : WordTrace (prefixWord ++ tailWord_1916626) baseStart_1916626 baseEnd_1916626 := by
    simpa [prefixWord, tailWord_1916626, baseEnd_1916626] using wordTrace_append hprefix tailTrace_1916626
  have hstable : (prefixWord ++ tailWord_1916626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916626).length < 2 ^ (prefixWord ++ tailWord_1916626).sum := by decide
  have hdescent : baseEnd_1916626 < baseStart_1916626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916643 : List Nat := [1, 1, 1, 7, 2, 1, 2, 6]
def baseStart_1916643 : Nat := 118140960795 + 1916643 * 2 ^ 59
def prefixEnd_1916643 : Nat := 4983230072969 + 3 ^ 40 * 1916643 * 2
def baseEnd_1916643 : Nat := 145801348455622201355263

theorem tailTrace_1916643 : CollatzResearch.WordTrace tailWord_1916643 prefixEnd_1916643 145801348455622201355263 := by
  unfold tailWord_1916643
  simp only [CollatzResearch.WordTrace]
  refine ⟨69905713195337222408914583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46603808796891481605943055 69905713195337222408914583)
  ·
    refine ⟨104858569793005833613371875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69905713195337222408914583 104858569793005833613371875)
    ·
      refine ⟨157287854689508750420057813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104858569793005833613371875 157287854689508750420057813)
      ·
        refine ⟨3686434094285361337970105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 157287854689508750420057813 3686434094285361337970105)
        ·
          refine ⟨2764825570714021003477579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3686434094285361337970105 2764825570714021003477579)
          ·
            refine ⟨4147238356071031505216369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2764825570714021003477579 4147238356071031505216369)
            ·
              refine ⟨3110428767053273628912277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4147238356071031505216369 3110428767053273628912277)
              ·
                refine ⟨145801348455622201355263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3110428767053273628912277 145801348455622201355263)
                ·
                  rfl

theorem cell21_1916643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 6].length) (baseStart_1916643 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1916643 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1916643 prefixEnd_1916643 := by exact prefixLift 1916643
  have htrace : WordTrace (prefixWord ++ tailWord_1916643) baseStart_1916643 baseEnd_1916643 := by
    simpa [prefixWord, tailWord_1916643, baseEnd_1916643] using wordTrace_append hprefix tailTrace_1916643
  have hstable : (prefixWord ++ tailWord_1916643).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916643).length < 2 ^ (prefixWord ++ tailWord_1916643).sum := by decide
  have hdescent : baseEnd_1916643 < baseStart_1916643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916660 : List Nat := [2, 6, 1, 1, 1, 1, 2, 7]
def baseStart_1916660 : Nat := 118140960795 + 1916660 * 2 ^ 59
def prefixEnd_1916660 : Nat := 4983230072969 + 3 ^ 40 * 1916660 * 2
def baseEnd_1916660 : Nat := 145802641666159450760807

theorem tailTrace_1916660 : CollatzResearch.WordTrace tailWord_1916660 prefixEnd_1916660 145802641666159450760807 := by
  unfold tailWord_1916660
  simp only [CollatzResearch.WordTrace]
  refine ⟨34953166618137817156141717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46604222157517089541522289 34953166618137817156141717)
  ·
    refine ⟨1638429685225210179194143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34953166618137817156141717 1638429685225210179194143)
    ·
      refine ⟨2457644527837815268791215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1638429685225210179194143 2457644527837815268791215)
      ·
        refine ⟨3686466791756722903186823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2457644527837815268791215 3686466791756722903186823)
        ·
          refine ⟨5529700187635084354780235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3686466791756722903186823 5529700187635084354780235)
          ·
            refine ⟨8294550281452626532170353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5529700187635084354780235 8294550281452626532170353)
            ·
              refine ⟨6220912711089469899127765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8294550281452626532170353 6220912711089469899127765)
              ·
                refine ⟨145802641666159450760807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6220912711089469899127765 145802641666159450760807)
                ·
                  rfl

theorem cell21_1916660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 7].length) (baseStart_1916660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1916660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1916660 prefixEnd_1916660 := by exact prefixLift 1916660
  have htrace : WordTrace (prefixWord ++ tailWord_1916660) baseStart_1916660 baseEnd_1916660 := by
    simpa [prefixWord, tailWord_1916660, baseEnd_1916660] using wordTrace_append hprefix tailTrace_1916660
  have hstable : (prefixWord ++ tailWord_1916660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916660).length < 2 ^ (prefixWord ++ tailWord_1916660).sum := by decide
  have hdescent : baseEnd_1916660 < baseStart_1916660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916716 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 7]
def baseStart_1916716 : Nat := 118140960795 + 1916716 * 2 ^ 59
def prefixEnd_1916716 : Nat := 4983230072969 + 3 ^ 40 * 1916716 * 2
def baseEnd_1916716 : Nat := 437420704961434699348973

theorem tailTrace_1916716 : CollatzResearch.WordTrace tailWord_1916716 prefixEnd_1916716 437420704961434699348973 := by
  unfold tailWord_1916716
  simp only [CollatzResearch.WordTrace]
  refine ⟨34954187862036377938161001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46605583816048503917548001 34954187862036377938161001)
  ·
    refine ⟨26215640896527283453620751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34954187862036377938161001 26215640896527283453620751)
    ·
      refine ⟨39323461344790925180431127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26215640896527283453620751 39323461344790925180431127)
      ·
        refine ⟨58985192017186387770646691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39323461344790925180431127 58985192017186387770646691)
        ·
          refine ⟨88477788025779581655970037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58985192017186387770646691 88477788025779581655970037)
          ·
            refine ⟨8294792627416835780247191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88477788025779581655970037 8294792627416835780247191)
            ·
              refine ⟨12442188941125253670370787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8294792627416835780247191 12442188941125253670370787)
              ·
                refine ⟨18663283411687880505556181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12442188941125253670370787 18663283411687880505556181)
                ·
                  refine ⟨437420704961434699348973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18663283411687880505556181 437420704961434699348973)
                  ·
                    rfl

theorem cell21_1916716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_1916716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1916716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1916716 prefixEnd_1916716 := by exact prefixLift 1916716
  have htrace : WordTrace (prefixWord ++ tailWord_1916716) baseStart_1916716 baseEnd_1916716 := by
    simpa [prefixWord, tailWord_1916716, baseEnd_1916716] using wordTrace_append hprefix tailTrace_1916716
  have hstable : (prefixWord ++ tailWord_1916716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916716).length < 2 ^ (prefixWord ++ tailWord_1916716).sum := by decide
  have hdescent : baseEnd_1916716 < baseStart_1916716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916761 : List Nat := [1, 2, 1, 2, 2, 3, 2, 8]
def baseStart_1916761 : Nat := 118140960795 + 1916761 * 2 ^ 59
def prefixEnd_1916761 : Nat := 4983230072969 + 3 ^ 40 * 1916761 * 2
def baseEnd_1916761 : Nat := 145810324858174873699627

theorem tailTrace_1916761 : CollatzResearch.WordTrace tailWord_1916761 prefixEnd_1916761 145810324858174873699627 := by
  unfold tailWord_1916761
  simp only [CollatzResearch.WordTrace]
  refine ⟨69910017008909728561710137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46606678005939819041140091 69910017008909728561710137)
  ·
    refine ⟨52432512756682296421282603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69910017008909728561710137 52432512756682296421282603)
    ·
      refine ⟨78648769135023444631923905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52432512756682296421282603 78648769135023444631923905)
      ·
        refine ⟨58986576851267583473942929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78648769135023444631923905 58986576851267583473942929)
        ·
          refine ⟨44239932638450687605457197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58986576851267583473942929 44239932638450687605457197)
          ·
            refine ⟨16589974739419007852046449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44239932638450687605457197 16589974739419007852046449)
            ·
              refine ⟨12442481054564255889034837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16589974739419007852046449 12442481054564255889034837)
              ·
                refine ⟨145810324858174873699627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12442481054564255889034837 145810324858174873699627)
                ·
                  rfl

theorem cell21_1916761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 8].length) (baseStart_1916761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1916761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1916761 prefixEnd_1916761 := by exact prefixLift 1916761
  have htrace : WordTrace (prefixWord ++ tailWord_1916761) baseStart_1916761 baseEnd_1916761 := by
    simpa [prefixWord, tailWord_1916761, baseEnd_1916761] using wordTrace_append hprefix tailTrace_1916761
  have hstable : (prefixWord ++ tailWord_1916761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916761).length < 2 ^ (prefixWord ++ tailWord_1916761).sum := by decide
  have hdescent : baseEnd_1916761 < baseStart_1916761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916885 : List Nat := [1, 3, 2, 3, 2, 2, 1, 2, 5]
def baseStart_1916885 : Nat := 118140960795 + 1916885 * 2 ^ 59
def prefixEnd_1916885 : Nat := 4983230072969 + 3 ^ 40 * 1916885 * 2
def baseEnd_1916885 : Nat := 437459273063927961031961

theorem tailTrace_1916885 : CollatzResearch.WordTrace tailWord_1916885 prefixEnd_1916885 437459273063927961031961 := by
  unfold tailWord_1916885
  simp only [CollatzResearch.WordTrace]
  refine ⟨69914539660460497739224109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46609693106973665159482739 69914539660460497739224109)
  ·
    refine ⟨26217952372672686652209041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69914539660460497739224109 26217952372672686652209041)
    ·
      refine ⟨19663464279504514989156781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26217952372672686652209041 19663464279504514989156781)
      ·
        refine ⟨7373799104814193120933793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19663464279504514989156781 7373799104814193120933793)
        ·
          refine ⟨5530349328610644840700345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7373799104814193120933793 5530349328610644840700345)
          ·
            refine ⟨4147761996457983630525259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5530349328610644840700345 4147761996457983630525259)
            ·
              refine ⟨6221642994686975445787889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4147761996457983630525259 6221642994686975445787889)
              ·
                refine ⟨4666232246015231584340917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6221642994686975445787889 4666232246015231584340917)
                ·
                  refine ⟨437459273063927961031961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4666232246015231584340917 437459273063927961031961)
                  ·
                    rfl

theorem cell21_1916885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_1916885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1916885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1916885 prefixEnd_1916885 := by exact prefixLift 1916885
  have htrace : WordTrace (prefixWord ++ tailWord_1916885) baseStart_1916885 baseEnd_1916885 := by
    simpa [prefixWord, tailWord_1916885, baseEnd_1916885] using wordTrace_append hprefix tailTrace_1916885
  have hstable : (prefixWord ++ tailWord_1916885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916885).length < 2 ^ (prefixWord ++ tailWord_1916885).sum := by decide
  have hdescent : baseEnd_1916885 < baseStart_1916885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916992 : List Nat := [2, 1, 1, 2, 2, 4, 4, 1, 4]
def baseStart_1916992 : Nat := 118140960795 + 1916992 * 2 ^ 59
def prefixEnd_1916992 : Nat := 4983230072969 + 3 ^ 40 * 1916992 * 2
def baseEnd_1916992 : Nat := 437483691921719552748409

theorem tailTrace_1916992 : CollatzResearch.WordTrace tailWord_1916992 prefixEnd_1916992 437483691921719552748409 := by
  unfold tailWord_1916992
  simp only [CollatzResearch.WordTrace]
  refine ⟨34959221135536427506684615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46612294847381903342246153 34959221135536427506684615)
  ·
    refine ⟨52438831703304641260026923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34959221135536427506684615 52438831703304641260026923)
    ·
      refine ⟨78658247554956961890040385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52438831703304641260026923 78658247554956961890040385)
      ·
        refine ⟨58993685666217721417530289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78658247554956961890040385 58993685666217721417530289)
        ·
          refine ⟨44245264249663291063147717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58993685666217721417530289 44245264249663291063147717)
          ·
            refine ⟨8295987046811867074340197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44245264249663291063147717 8295987046811867074340197)
            ·
              refine ⟨1555497571277225076438787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8295987046811867074340197 1555497571277225076438787)
              ·
                refine ⟨2333246356915837614658181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1555497571277225076438787 2333246356915837614658181)
                ·
                  refine ⟨437483691921719552748409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2333246356915837614658181 437483691921719552748409)
                  ·
                    rfl

theorem cell21_1916992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 4].length) (baseStart_1916992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1916992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1916992 prefixEnd_1916992 := by exact prefixLift 1916992
  have htrace : WordTrace (prefixWord ++ tailWord_1916992) baseStart_1916992 baseEnd_1916992 := by
    simpa [prefixWord, tailWord_1916992, baseEnd_1916992] using wordTrace_append hprefix tailTrace_1916992
  have hstable : (prefixWord ++ tailWord_1916992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916992).length < 2 ^ (prefixWord ++ tailWord_1916992).sum := by decide
  have hdescent : baseEnd_1916992 < baseStart_1916992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917082 : List Nat := [3, 1, 1, 5, 2, 1, 8]
def baseStart_1917082 : Nat := 118140960795 + 1917082 * 2 ^ 59
def prefixEnd_1917082 : Nat := 4983230072969 + 3 ^ 40 * 1917082 * 2
def baseEnd_1917082 : Nat := 48611581238655488472025

theorem tailTrace_1917082 : CollatzResearch.WordTrace tailWord_1917082 prefixEnd_1917082 48611581238655488472025 := by
  unfold tailWord_1917082
  simp only [CollatzResearch.WordTrace]
  refine ⟨17480431210186700096036375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46614483227164533589430333 17480431210186700096036375)
  ·
    refine ⟨26220646815280050144054563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17480431210186700096036375 26220646815280050144054563)
    ·
      refine ⟨39330970222920075216081845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26220646815280050144054563 39330970222920075216081845)
      ·
        refine ⟨3687278458398757051507673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39330970222920075216081845 3687278458398757051507673)
        ·
          refine ⟨2765458843799067788630755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3687278458398757051507673 2765458843799067788630755)
          ·
            refine ⟨4148188265698601682946133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2765458843799067788630755 4148188265698601682946133)
            ·
              refine ⟨48611581238655488472025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4148188265698601682946133 48611581238655488472025)
              ·
                rfl

theorem cell21_1917082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 8].length) (baseStart_1917082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1917082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1917082 prefixEnd_1917082 := by exact prefixLift 1917082
  have htrace : WordTrace (prefixWord ++ tailWord_1917082) baseStart_1917082 baseEnd_1917082 := by
    simpa [prefixWord, tailWord_1917082, baseEnd_1917082] using wordTrace_append hprefix tailTrace_1917082
  have hstable : (prefixWord ++ tailWord_1917082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917082).length < 2 ^ (prefixWord ++ tailWord_1917082).sum := by decide
  have hdescent : baseEnd_1917082 < baseStart_1917082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917116 : List Nat := [2, 2, 2, 3, 4, 1, 2, 5]
def baseStart_1917116 : Nat := 118140960795 + 1917116 * 2 ^ 59
def prefixEnd_1917116 : Nat := 4983230072969 + 3 ^ 40 * 1917116 * 2
def baseEnd_1917116 : Nat := 145837330137040964227163

theorem tailTrace_1917116 : CollatzResearch.WordTrace tailWord_1917116 prefixEnd_1917116 145837330137040964227163 := by
  unfold tailWord_1917116
  simp only [CollatzResearch.WordTrace]
  refine ⟨34961482461311812095441601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46615309948415749460588801 34961482461311812095441601)
  ·
    refine ⟨26221111845983859071581201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34961482461311812095441601 26221111845983859071581201)
    ·
      refine ⟨19665833884487894303685901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26221111845983859071581201 19665833884487894303685901)
      ·
        refine ⟨7374687706682960363882213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19665833884487894303685901 7374687706682960363882213)
        ·
          refine ⟨1382753945003055068227915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7374687706682960363882213 1382753945003055068227915)
          ·
            refine ⟨2074130917504582602341873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1382753945003055068227915 2074130917504582602341873)
            ·
              refine ⟨1555598188128436951756405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2074130917504582602341873 1555598188128436951756405)
              ·
                refine ⟨145837330137040964227163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1555598188128436951756405 145837330137040964227163)
                ·
                  rfl

theorem cell21_1917116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 5].length) (baseStart_1917116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1917116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1917116 prefixEnd_1917116 := by exact prefixLift 1917116
  have htrace : WordTrace (prefixWord ++ tailWord_1917116) baseStart_1917116 baseEnd_1917116 := by
    simpa [prefixWord, tailWord_1917116, baseEnd_1917116] using wordTrace_append hprefix tailTrace_1917116
  have hstable : (prefixWord ++ tailWord_1917116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917116).length < 2 ^ (prefixWord ++ tailWord_1917116).sum := by decide
  have hdescent : baseEnd_1917116 < baseStart_1917116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917217 : List Nat := [1, 2, 3, 2, 1, 1, 5, 6]
def baseStart_1917217 : Nat := 118140960795 + 1917217 * 2 ^ 59
def prefixEnd_1917217 : Nat := 4983230072969 + 3 ^ 40 * 1917217 * 2
def baseEnd_1917217 : Nat := 145845013329056387165983

theorem tailTrace_1917217 : CollatzResearch.WordTrace tailWord_1917217 prefixEnd_1917217 145845013329056387165983 := by
  unfold tailWord_1917217
  simp only [CollatzResearch.WordTrace]
  refine ⟨69926648695257718440309905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46617765796838478960206603 69926648695257718440309905)
  ·
    refine ⟨52444986521443288830232429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69926648695257718440309905 52444986521443288830232429)
    ·
      refine ⟨19666869945541233311337161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52444986521443288830232429 19666869945541233311337161)
      ·
        refine ⟨14750152459155924983502871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19666869945541233311337161 14750152459155924983502871)
        ·
          refine ⟨22125228688733887475254307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14750152459155924983502871 22125228688733887475254307)
          ·
            refine ⟨33187843033100831212881461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22125228688733887475254307 33187843033100831212881461)
            ·
              refine ⟨3111360284353202926207637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33187843033100831212881461 3111360284353202926207637)
              ·
                refine ⟨145845013329056387165983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3111360284353202926207637 145845013329056387165983)
                ·
                  rfl

theorem cell21_1917217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 6].length) (baseStart_1917217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1917217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1917217 prefixEnd_1917217 := by exact prefixLift 1917217
  have htrace : WordTrace (prefixWord ++ tailWord_1917217) baseStart_1917217 baseEnd_1917217 := by
    simpa [prefixWord, tailWord_1917217, baseEnd_1917217] using wordTrace_append hprefix tailTrace_1917217
  have hstable : (prefixWord ++ tailWord_1917217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917217).length < 2 ^ (prefixWord ++ tailWord_1917217).sum := by decide
  have hdescent : baseEnd_1917217 < baseStart_1917217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917223 : List Nat := [1, 1, 8, 1, 1, 1, 1, 2, 5]
def baseStart_1917223 : Nat := 118140960795 + 1917223 * 2 ^ 59
def prefixEnd_1917223 : Nat := 4983230072969 + 3 ^ 40 * 1917223 * 2
def baseEnd_1917223 : Nat := 437536409268914484397937

theorem tailTrace_1917223 : CollatzResearch.WordTrace tailWord_1917223 prefixEnd_1917223 437536409268914484397937 := by
  unfold tailWord_1917223
  simp only [CollatzResearch.WordTrace]
  refine ⟨69926867533235981465028323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46617911688823987643352215 69926867533235981465028323)
  ·
    refine ⟨104890301299853972197542485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69926867533235981465028323 104890301299853972197542485)
    ·
      refine ⟨1229183218357663736689951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 104890301299853972197542485 1229183218357663736689951)
      ·
        refine ⟨1843774827536495605034927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1229183218357663736689951 1843774827536495605034927)
        ·
          refine ⟨2765662241304743407552391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1843774827536495605034927 2765662241304743407552391)
          ·
            refine ⟨4148493361957115111328587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2765662241304743407552391 4148493361957115111328587)
            ·
              refine ⟨6222740042935672666992881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4148493361957115111328587 6222740042935672666992881)
              ·
                refine ⟨4667055032201754500244661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6222740042935672666992881 4667055032201754500244661)
                ·
                  refine ⟨437536409268914484397937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4667055032201754500244661 437536409268914484397937)
                  ·
                    rfl

theorem cell21_1917223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 5].length) (baseStart_1917223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1917223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1917223 prefixEnd_1917223 := by exact prefixLift 1917223
  have htrace : WordTrace (prefixWord ++ tailWord_1917223) baseStart_1917223 baseEnd_1917223 := by
    simpa [prefixWord, tailWord_1917223, baseEnd_1917223] using wordTrace_append hprefix tailTrace_1917223
  have hstable : (prefixWord ++ tailWord_1917223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917223).length < 2 ^ (prefixWord ++ tailWord_1917223).sum := by decide
  have hdescent : baseEnd_1917223 < baseStart_1917223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917231 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 7]
def baseStart_1917231 : Nat := 118140960795 + 1917231 * 2 ^ 59
def prefixEnd_1917231 : Nat := 4983230072969 + 3 ^ 40 * 1917231 * 2
def baseEnd_1917231 : Nat := 437538234977908248264587

theorem tailTrace_1917231 : CollatzResearch.WordTrace tailWord_1917231 prefixEnd_1917231 437538234977908248264587 := by
  unfold tailWord_1917231
  simp only [CollatzResearch.WordTrace]
  refine ⟨69927159317206998831319547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46618106211471332554213031 69927159317206998831319547)
  ·
    refine ⟨104890738975810498246979321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69927159317206998831319547 104890738975810498246979321)
    ·
      refine ⟨78668054231857873685234491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104890738975810498246979321 78668054231857873685234491)
      ·
        refine ⟨118002081347786810527851737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78668054231857873685234491 118002081347786810527851737)
        ·
          refine ⟨88501561010840107895888803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118002081347786810527851737 88501561010840107895888803)
          ·
            refine ⟨132752341516260161843833205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88501561010840107895888803 132752341516260161843833205)
            ·
              refine ⟨12445532017149390172859363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132752341516260161843833205 12445532017149390172859363)
              ·
                refine ⟨18668298025724085259289045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12445532017149390172859363 18668298025724085259289045)
                ·
                  refine ⟨437538234977908248264587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18668298025724085259289045 437538234977908248264587)
                  ·
                    rfl

theorem cell21_1917231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 7].length) (baseStart_1917231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1917231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1917231 prefixEnd_1917231 := by exact prefixLift 1917231
  have htrace : WordTrace (prefixWord ++ tailWord_1917231) baseStart_1917231 baseEnd_1917231 := by
    simpa [prefixWord, tailWord_1917231, baseEnd_1917231] using wordTrace_append hprefix tailTrace_1917231
  have hstable : (prefixWord ++ tailWord_1917231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917231).length < 2 ^ (prefixWord ++ tailWord_1917231).sum := by decide
  have hdescent : baseEnd_1917231 < baseStart_1917231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917265 : List Nat := [1, 2, 2, 1, 4, 2, 2, 4, 3]
def baseStart_1917265 : Nat := 118140960795 + 1917265 * 2 ^ 59
def prefixEnd_1917265 : Nat := 4983230072969 + 3 ^ 40 * 1917265 * 2
def baseEnd_1917265 : Nat := 437545994241131744697851

theorem tailTrace_1917265 : CollatzResearch.WordTrace tailWord_1917265 prefixEnd_1917265 437545994241131744697851 := by
  unfold tailWord_1917265
  simp only [CollatzResearch.WordTrace]
  refine ⟨69928399399083822638057249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46618932932722548425371499 69928399399083822638057249)
  ·
    refine ⟨52446299549312866978542937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69928399399083822638057249 52446299549312866978542937)
    ·
      refine ⟨39334724661984650233907203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52446299549312866978542937 39334724661984650233907203)
      ·
        refine ⟨59002086992976975350860805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39334724661984650233907203 59002086992976975350860805)
        ·
          refine ⟨11062891311183182878286401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59002086992976975350860805 11062891311183182878286401)
          ·
            refine ⟨8297168483387387158714801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11062891311183182878286401 8297168483387387158714801)
            ·
              refine ⟨6222876362540540369036101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8297168483387387158714801 6222876362540540369036101)
              ·
                refine ⟨1166789317976351319194269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6222876362540540369036101 1166789317976351319194269)
                ·
                  refine ⟨437545994241131744697851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1166789317976351319194269 437545994241131744697851)
                  ·
                    rfl

theorem cell21_1917265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4, 3].length) (baseStart_1917265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1917265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1917265 prefixEnd_1917265 := by exact prefixLift 1917265
  have htrace : WordTrace (prefixWord ++ tailWord_1917265) baseStart_1917265 baseEnd_1917265 := by
    simpa [prefixWord, tailWord_1917265, baseEnd_1917265] using wordTrace_append hprefix tailTrace_1917265
  have hstable : (prefixWord ++ tailWord_1917265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917265).length < 2 ^ (prefixWord ++ tailWord_1917265).sum := by decide
  have hdescent : baseEnd_1917265 < baseStart_1917265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917293 : List Nat := [1, 5, 1, 1, 1, 2, 3, 7]
def baseStart_1917293 : Nat := 118140960795 + 1917293 * 2 ^ 59
def prefixEnd_1917293 : Nat := 4983230072969 + 3 ^ 40 * 1917293 * 2
def baseEnd_1917293 : Nat := 145850794740869972743709

theorem tailTrace_1917293 : CollatzResearch.WordTrace tailWord_1917293 prefixEnd_1917293 145850794740869972743709 := by
  unfold tailWord_1917293
  simp only [CollatzResearch.WordTrace]
  refine ⟨69929420642982383420076533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46619613761988255613384355 69929420642982383420076533)
  ·
    refine ⟨6555883185279598445632175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69929420642982383420076533 6555883185279598445632175)
    ·
      refine ⟨9833824777919397668448263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6555883185279598445632175 9833824777919397668448263)
      ·
        refine ⟨14750737166879096502672395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9833824777919397668448263 14750737166879096502672395)
        ·
          refine ⟨22126105750318644754008593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14750737166879096502672395 22126105750318644754008593)
          ·
            refine ⟨16594579312738983565506445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22126105750318644754008593 16594579312738983565506445)
            ·
              refine ⟨6222967242277118837064917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16594579312738983565506445 6222967242277118837064917)
              ·
                refine ⟨145850794740869972743709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6222967242277118837064917 145850794740869972743709)
                ·
                  rfl

theorem cell21_1917293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 7].length) (baseStart_1917293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1917293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1917293 prefixEnd_1917293 := by exact prefixLift 1917293
  have htrace : WordTrace (prefixWord ++ tailWord_1917293) baseStart_1917293 baseEnd_1917293 := by
    simpa [prefixWord, tailWord_1917293, baseEnd_1917293] using wordTrace_append hprefix tailTrace_1917293
  have hstable : (prefixWord ++ tailWord_1917293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917293).length < 2 ^ (prefixWord ++ tailWord_1917293).sum := by decide
  have hdescent : baseEnd_1917293 < baseStart_1917293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917324 : List Nat := [2, 2, 1, 2, 1, 4, 3, 1, 5]
def baseStart_1917324 : Nat := 118140960795 + 1917324 * 2 ^ 59
def prefixEnd_1917324 : Nat := 4983230072969 + 3 ^ 40 * 1917324 * 2
def baseEnd_1917324 : Nat := 437559458844960753214397

theorem tailTrace_1917324 : CollatzResearch.WordTrace tailWord_1917324 prefixEnd_1917324 437559458844960753214397 := by
  unfold tailWord_1917324
  simp only [CollatzResearch.WordTrace]
  refine ⟨34965275652935037857227513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46620367537246717142970017 34965275652935037857227513)
  ·
    refine ⟨26223956739701278392920635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34965275652935037857227513 26223956739701278392920635)
    ·
      refine ⟨39335935109551917589380953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26223956739701278392920635 39335935109551917589380953)
      ·
        refine ⟨29501951332163938192035715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39335935109551917589380953 29501951332163938192035715)
        ·
          refine ⟨44252926998245907288053573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29501951332163938192035715 44252926998245907288053573)
          ·
            refine ⟨8297423812171107616510045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44252926998245907288053573 8297423812171107616510045)
            ·
              refine ⟨3111533929564165356191267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8297423812171107616510045 3111533929564165356191267)
              ·
                refine ⟨4667300894346248034286901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3111533929564165356191267 4667300894346248034286901)
                ·
                  refine ⟨437559458844960753214397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4667300894346248034286901 437559458844960753214397)
                  ·
                    rfl

theorem cell21_1917324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_1917324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1917324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1917324 prefixEnd_1917324 := by exact prefixLift 1917324
  have htrace : WordTrace (prefixWord ++ tailWord_1917324) baseStart_1917324 baseEnd_1917324 := by
    simpa [prefixWord, tailWord_1917324, baseEnd_1917324] using wordTrace_append hprefix tailTrace_1917324
  have hstable : (prefixWord ++ tailWord_1917324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917324).length < 2 ^ (prefixWord ++ tailWord_1917324).sum := by decide
  have hdescent : baseEnd_1917324 < baseStart_1917324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917372 : List Nat := [2, 2, 2, 4, 1, 2, 2, 2, 4]
def baseStart_1917372 : Nat := 118140960795 + 1917372 * 2 ^ 59
def prefixEnd_1917372 : Nat := 4983230072969 + 3 ^ 40 * 1917372 * 2
def baseEnd_1917372 : Nat := 437570413098923336414299

theorem tailTrace_1917372 : CollatzResearch.WordTrace tailWord_1917372 prefixEnd_1917372 437570413098923336414299 := by
  unfold tailWord_1917372
  simp only [CollatzResearch.WordTrace]
  refine ⟨34966151004848089956101185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46621534673130786608134913 34966151004848089956101185)
  ·
    refine ⟨26224613253636067467075889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34966151004848089956101185 26224613253636067467075889)
    ·
      refine ⟨19668459940227050600306917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26224613253636067467075889 19668459940227050600306917)
      ·
        refine ⟨3687836238792571987557547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19668459940227050600306917 3687836238792571987557547)
        ·
          refine ⟨5531754358188857981336321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3687836238792571987557547 5531754358188857981336321)
          ·
            refine ⟨4148815768641643486002241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5531754358188857981336321 4148815768641643486002241)
            ·
              refine ⟨3111611826481232614501681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4148815768641643486002241 3111611826481232614501681)
              ·
                refine ⟨2333708869860924460876261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3111611826481232614501681 2333708869860924460876261)
                ·
                  refine ⟨437570413098923336414299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2333708869860924460876261 437570413098923336414299)
                  ·
                    rfl

theorem cell21_1917372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_1917372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1917372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1917372 prefixEnd_1917372 := by exact prefixLift 1917372
  have htrace : WordTrace (prefixWord ++ tailWord_1917372) baseStart_1917372 baseEnd_1917372 := by
    simpa [prefixWord, tailWord_1917372, baseEnd_1917372] using wordTrace_append hprefix tailTrace_1917372
  have hstable : (prefixWord ++ tailWord_1917372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917372).length < 2 ^ (prefixWord ++ tailWord_1917372).sum := by decide
  have hdescent : baseEnd_1917372 < baseStart_1917372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917459 : List Nat := [1, 1, 1, 2, 1, 5, 1, 4, 5]
def baseStart_1917459 : Nat := 118140960795 + 1917459 * 2 ^ 59
def prefixEnd_1917459 : Nat := 4983230072969 + 3 ^ 40 * 1917459 * 2
def baseEnd_1917459 : Nat := 437590267684230518464121

theorem tailTrace_1917459 : CollatzResearch.WordTrace tailWord_1917459 prefixEnd_1917459 437590267684230518464121 := by
  unfold tailWord_1917459
  simp only [CollatzResearch.WordTrace]
  refine ⟨69935475160380993770619431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46623650106920662513746287 69935475160380993770619431)
  ·
    refine ⟨104903212740571490655929147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69935475160380993770619431 104903212740571490655929147)
    ·
      refine ⟨157354819110857235983893721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104903212740571490655929147 157354819110857235983893721)
      ·
        refine ⟨118016114333142926987920291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157354819110857235983893721 118016114333142926987920291)
        ·
          refine ⟨177024171499714390481880437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118016114333142926987920291 177024171499714390481880437)
          ·
            refine ⟨16596016078098224107676291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 177024171499714390481880437 16596016078098224107676291)
            ·
              refine ⟨24894024117147336161514437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16596016078098224107676291 24894024117147336161514437)
              ·
                refine ⟨4667629521965125530283957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24894024117147336161514437 4667629521965125530283957)
                ·
                  refine ⟨437590267684230518464121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4667629521965125530283957 437590267684230518464121)
                  ·
                    rfl

theorem cell21_1917459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 5].length) (baseStart_1917459 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1917459 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1917459 prefixEnd_1917459 := by exact prefixLift 1917459
  have htrace : WordTrace (prefixWord ++ tailWord_1917459) baseStart_1917459 baseEnd_1917459 := by
    simpa [prefixWord, tailWord_1917459, baseEnd_1917459] using wordTrace_append hprefix tailTrace_1917459
  have hstable : (prefixWord ++ tailWord_1917459).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917459).length < 2 ^ (prefixWord ++ tailWord_1917459).sum := by decide
  have hdescent : baseEnd_1917459 < baseStart_1917459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917479 : List Nat := [1, 1, 7, 2, 1, 2, 7]
def baseStart_1917479 : Nat := 118140960795 + 1917479 * 2 ^ 59
def prefixEnd_1917479 : Nat := 4983230072969 + 3 ^ 40 * 1917479 * 2
def baseEnd_1917479 : Nat := 48621647995190547570083

theorem tailTrace_1917479 : CollatzResearch.WordTrace tailWord_1917479 prefixEnd_1917479 48621647995190547570083 := by
  unfold tailWord_1917479
  simp only [CollatzResearch.WordTrace]
  refine ⟨69936204620308537186347491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46624136413539024790898327 69936204620308537186347491)
  ·
    refine ⟨104904306930462805779521237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69936204620308537186347491 104904306930462805779521237)
    ·
      refine ⟨2458694693682722010457529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 104904306930462805779521237 2458694693682722010457529)
      ·
        refine ⟨1844021020262041507843147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2458694693682722010457529 1844021020262041507843147)
        ·
          refine ⟨2766031530393062261764721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1844021020262041507843147 2766031530393062261764721)
          ·
            refine ⟨2074523647794796696323541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2766031530393062261764721 2074523647794796696323541)
            ·
              refine ⟨48621647995190547570083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2074523647794796696323541 48621647995190547570083)
              ·
                rfl

theorem cell21_1917479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 7].length) (baseStart_1917479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1917479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1917479 prefixEnd_1917479 := by exact prefixLift 1917479
  have htrace : WordTrace (prefixWord ++ tailWord_1917479) baseStart_1917479 baseEnd_1917479 := by
    simpa [prefixWord, tailWord_1917479, baseEnd_1917479] using wordTrace_append hprefix tailTrace_1917479
  have hstable : (prefixWord ++ tailWord_1917479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917479).length < 2 ^ (prefixWord ++ tailWord_1917479).sum := by decide
  have hdescent : baseEnd_1917479 < baseStart_1917479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917485 : List Nat := [1, 5, 4, 1, 1, 1, 3, 2, 3]
def baseStart_1917485 : Nat := 118140960795 + 1917485 * 2 ^ 59
def prefixEnd_1917485 : Nat := 4983230072969 + 3 ^ 40 * 1917485 * 2
def baseEnd_1917485 : Nat := 437596201238460251030735

theorem tailTrace_1917485 : CollatzResearch.WordTrace tailWord_1917485 prefixEnd_1917485 437596201238460251030735 := by
  unfold tailWord_1917485
  simp only [CollatzResearch.WordTrace]
  refine ⟨69936423458286800211065909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46624282305524533474043939 69936423458286800211065909)
  ·
    refine ⟨6556539699214387519787429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69936423458286800211065909 6556539699214387519787429)
    ·
      refine ⟨1229351193602697659960143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6556539699214387519787429 1229351193602697659960143)
      ·
        refine ⟨1844026790404046489940215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1229351193602697659960143 1844026790404046489940215)
        ·
          refine ⟨2766040185606069734910323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1844026790404046489940215 2766040185606069734910323)
          ·
            refine ⟨4149060278409104602365485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2766040185606069734910323 4149060278409104602365485)
            ·
              refine ⟨1555897604403414225887057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4149060278409104602365485 1555897604403414225887057)
              ·
                refine ⟨1166923203302560669415293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1555897604403414225887057 1166923203302560669415293)
                ·
                  refine ⟨437596201238460251030735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1166923203302560669415293 437596201238460251030735)
                  ·
                    rfl

theorem cell21_1917485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_1917485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1917485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1917485 prefixEnd_1917485 := by exact prefixLift 1917485
  have htrace : WordTrace (prefixWord ++ tailWord_1917485) baseStart_1917485 baseEnd_1917485 := by
    simpa [prefixWord, tailWord_1917485, baseEnd_1917485] using wordTrace_append hprefix tailTrace_1917485
  have hstable : (prefixWord ++ tailWord_1917485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917485).length < 2 ^ (prefixWord ++ tailWord_1917485).sum := by decide
  have hdescent : baseEnd_1917485 < baseStart_1917485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917490 : List Nat := [3, 2, 1, 1, 2, 1, 4, 1, 6]
def baseStart_1917490 : Nat := 118140960795 + 1917490 * 2 ^ 59
def prefixEnd_1917490 : Nat := 4983230072969 + 3 ^ 40 * 1917490 * 2
def baseEnd_1917490 : Nat := 437597342306581353447391

theorem tailTrace_1917490 : CollatzResearch.WordTrace tailWord_1917490 prefixEnd_1917490 437597342306581353447391 := by
  unfold tailWord_1917490
  simp only [CollatzResearch.WordTrace]
  refine ⟨17484151455817171516249481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46624403882179124043331949 17484151455817171516249481)
  ·
    refine ⟨13113113591862878637187111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17484151455817171516249481 13113113591862878637187111)
    ·
      refine ⟨19669670387794317955780667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13113113591862878637187111 19669670387794317955780667)
      ·
        refine ⟨29504505581691476933671001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19669670387794317955780667 29504505581691476933671001)
        ·
          refine ⟨22128379186268607700253251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29504505581691476933671001 22128379186268607700253251)
          ·
            refine ⟨33192568779402911550379877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22128379186268607700253251 33192568779402911550379877)
            ·
              refine ⟨6223606646138045915696227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33192568779402911550379877 6223606646138045915696227)
              ·
                refine ⟨9335409969207068873544341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6223606646138045915696227 9335409969207068873544341)
                ·
                  refine ⟨437597342306581353447391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9335409969207068873544341 437597342306581353447391)
                  ·
                    rfl

theorem cell21_1917490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_1917490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1917490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1917490 prefixEnd_1917490 := by exact prefixLift 1917490
  have htrace : WordTrace (prefixWord ++ tailWord_1917490) baseStart_1917490 baseEnd_1917490 := by
    simpa [prefixWord, tailWord_1917490, baseEnd_1917490] using wordTrace_append hprefix tailTrace_1917490
  have hstable : (prefixWord ++ tailWord_1917490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917490).length < 2 ^ (prefixWord ++ tailWord_1917490).sum := by decide
  have hdescent : baseEnd_1917490 < baseStart_1917490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917504 : List Nat := [2, 1, 1, 2, 2, 2, 3, 8]
def baseStart_1917504 : Nat := 118140960795 + 1917504 * 2 ^ 59
def prefixEnd_1917504 : Nat := 4983230072969 + 3 ^ 40 * 1917504 * 2
def baseEnd_1917504 : Nat := 145866845765773480071343

theorem tailTrace_1917504 : CollatzResearch.WordTrace tailWord_1917504 prefixEnd_1917504 145866845765773480071343 := by
  unfold tailWord_1917504
  simp only [CollatzResearch.WordTrace]
  refine ⟨34968558222608983228003783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46624744296811977637338377 34968558222608983228003783)
  ·
    refine ⟨52452837333913474842005675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34968558222608983228003783 52452837333913474842005675)
    ·
      refine ⟨78679256000870212263008513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52452837333913474842005675 78679256000870212263008513)
      ·
        refine ⟨59009442000652659197256385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78679256000870212263008513 59009442000652659197256385)
        ·
          refine ⟨44257081500489494397942289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59009442000652659197256385 44257081500489494397942289)
          ·
            refine ⟨33192811125367120798456717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44257081500489494397942289 33192811125367120798456717)
            ·
              refine ⟨12447304172012670299421269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33192811125367120798456717 12447304172012670299421269)
              ·
                refine ⟨145866845765773480071343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12447304172012670299421269 145866845765773480071343)
                ·
                  rfl

theorem cell21_1917504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 8].length) (baseStart_1917504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1917504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1917504 prefixEnd_1917504 := by exact prefixLift 1917504
  have htrace : WordTrace (prefixWord ++ tailWord_1917504) baseStart_1917504 baseEnd_1917504 := by
    simpa [prefixWord, tailWord_1917504, baseEnd_1917504] using wordTrace_append hprefix tailTrace_1917504
  have hstable : (prefixWord ++ tailWord_1917504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917504).length < 2 ^ (prefixWord ++ tailWord_1917504).sum := by decide
  have hdescent : baseEnd_1917504 < baseStart_1917504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917538 : List Nat := [3, 3, 2, 3, 1, 9]
def baseStart_1917538 : Nat := 118140960795 + 1917538 * 2 ^ 59
def prefixEnd_1917538 : Nat := 4983230072969 + 3 ^ 40 * 1917538 * 2
def baseEnd_1917538 : Nat := 16207714687427553209159

theorem tailTrace_1917538 : CollatzResearch.WordTrace tailWord_1917538 prefixEnd_1917538 16207714687427553209159 := by
  unfold tailWord_1917538
  simp only [CollatzResearch.WordTrace]
  refine ⟨17484589131773697565686317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46625571018063193508496845 17484589131773697565686317)
  ·
    refine ⟨6556720924415136587132369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17484589131773697565686317 6556720924415136587132369)
    ·
      refine ⟨4917540693311352440349277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6556720924415136587132369 4917540693311352440349277)
      ·
        refine ⟨1844077759991757165130979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4917540693311352440349277 1844077759991757165130979)
        ·
          refine ⟨2766116639987635747696469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1844077759991757165130979 2766116639987635747696469)
          ·
            refine ⟨16207714687427553209159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2766116639987635747696469 16207714687427553209159)
            ·
              rfl

theorem cell21_1917538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 9].length) (baseStart_1917538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1917538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1917538 prefixEnd_1917538 := by exact prefixLift 1917538
  have htrace : WordTrace (prefixWord ++ tailWord_1917538) baseStart_1917538 baseEnd_1917538 := by
    simpa [prefixWord, tailWord_1917538, baseEnd_1917538] using wordTrace_append hprefix tailTrace_1917538
  have hstable : (prefixWord ++ tailWord_1917538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917538).length < 2 ^ (prefixWord ++ tailWord_1917538).sum := by decide
  have hdescent : baseEnd_1917538 < baseStart_1917538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917544 : List Nat := [2, 1, 4, 3, 3, 1, 2, 2, 3]
def baseStart_1917544 : Nat := 118140960795 + 1917544 * 2 ^ 59
def prefixEnd_1917544 : Nat := 4983230072969 + 3 ^ 40 * 1917544 * 2
def baseEnd_1917544 : Nat := 437609665842289259547281

theorem tailTrace_1917544 : CollatzResearch.WordTrace tailWord_1917544 prefixEnd_1917544 437609665842289259547281 := by
  unfold tailWord_1917544
  simp only [CollatzResearch.WordTrace]
  refine ⟨34969287682536526643731843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46625716910048702191642457 34969287682536526643731843)
  ·
    refine ⟨52453931523804789965597765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34969287682536526643731843 52453931523804789965597765)
    ·
      refine ⟨9835112160713398118549581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52453931523804789965597765 9835112160713398118549581)
      ·
        refine ⟨3688167060267524294456093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9835112160713398118549581 3688167060267524294456093)
        ·
          refine ⟨1383062647600321610421035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3688167060267524294456093 1383062647600321610421035)
          ·
            refine ⟨2074593971400482415631553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1383062647600321610421035 2074593971400482415631553)
            ·
              refine ⟨1555945478550361811723665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2074593971400482415631553 1555945478550361811723665)
              ·
                refine ⟨1166959108912771358792749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1555945478550361811723665 1166959108912771358792749)
                ·
                  refine ⟨437609665842289259547281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1166959108912771358792749 437609665842289259547281)
                  ·
                    rfl

theorem cell21_1917544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2, 3].length) (baseStart_1917544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1917544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1917544 prefixEnd_1917544 := by exact prefixLift 1917544
  have htrace : WordTrace (prefixWord ++ tailWord_1917544) baseStart_1917544 baseEnd_1917544 := by
    simpa [prefixWord, tailWord_1917544, baseEnd_1917544] using wordTrace_append hprefix tailTrace_1917544
  have hstable : (prefixWord ++ tailWord_1917544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917544).length < 2 ^ (prefixWord ++ tailWord_1917544).sum := by decide
  have hdescent : baseEnd_1917544 < baseStart_1917544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917586 : List Nat := [3, 2, 3, 1, 2, 2, 2, 3, 3]
def baseStart_1917586 : Nat := 118140960795 + 1917586 * 2 ^ 59
def prefixEnd_1917586 : Nat := 4983230072969 + 3 ^ 40 * 1917586 * 2
def baseEnd_1917586 : Nat := 437619250814506519847195

theorem tailTrace_1917586 : CollatzResearch.WordTrace tailWord_1917586 prefixEnd_1917586 437619250814506519847195 := by
  unfold tailWord_1917586
  simp only [CollatzResearch.WordTrace]
  refine ⟨17485026807730223615123153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46626738153947262973661741 17485026807730223615123153)
  ·
    refine ⟨13113770105797667711342365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17485026807730223615123153 13113770105797667711342365)
    ·
      refine ⟨4917663789674125391753387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13113770105797667711342365 4917663789674125391753387)
      ·
        refine ⟨7376495684511188087630081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4917663789674125391753387 7376495684511188087630081)
        ·
          refine ⟨5532371763383391065722561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7376495684511188087630081 5532371763383391065722561)
          ·
            refine ⟨4149278822537543299291921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5532371763383391065722561 4149278822537543299291921)
            ·
              refine ⟨3111959116903157474468941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4149278822537543299291921 3111959116903157474468941)
              ·
                refine ⟨1166984668838684052925853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3111959116903157474468941 1166984668838684052925853)
                ·
                  refine ⟨437619250814506519847195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1166984668838684052925853 437619250814506519847195)
                  ·
                    rfl

theorem cell21_1917586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_1917586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1917586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1917586 prefixEnd_1917586 := by exact prefixLift 1917586
  have htrace : WordTrace (prefixWord ++ tailWord_1917586) baseStart_1917586 baseEnd_1917586 := by
    simpa [prefixWord, tailWord_1917586, baseEnd_1917586] using wordTrace_append hprefix tailTrace_1917586
  have hstable : (prefixWord ++ tailWord_1917586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917586).length < 2 ^ (prefixWord ++ tailWord_1917586).sum := by decide
  have hdescent : baseEnd_1917586 < baseStart_1917586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917600 : List Nat := [2, 1, 1, 4, 4, 2, 1, 2, 4]
def baseStart_1917600 : Nat := 118140960795 + 1917600 * 2 ^ 59
def prefixEnd_1917600 : Nat := 4983230072969 + 3 ^ 40 * 1917600 * 2
def baseEnd_1917600 : Nat := 437622445805245606613833

theorem tailTrace_1917600 : CollatzResearch.WordTrace tailWord_1917600 prefixEnd_1917600 437622445805245606613833 := by
  unfold tailWord_1917600
  simp only [CollatzResearch.WordTrace]
  refine ⟨34970308926435087425751127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46627078568580116567668169 34970308926435087425751127)
  ·
    refine ⟨52455463389652631138626691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34970308926435087425751127 52455463389652631138626691)
    ·
      refine ⟨78683195084478946707940037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52455463389652631138626691 78683195084478946707940037)
      ·
        refine ⟨14753099078339802507738757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78683195084478946707940037 14753099078339802507738757)
        ·
          refine ⟨2766206077188712970201017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14753099078339802507738757 2766206077188712970201017)
          ·
            refine ⟨2074654557891534727650763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2766206077188712970201017 2074654557891534727650763)
            ·
              refine ⟨3111981836837302091476145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2074654557891534727650763 3111981836837302091476145)
              ·
                refine ⟨2333986377627976568607109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3111981836837302091476145 2333986377627976568607109)
                ·
                  refine ⟨437622445805245606613833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2333986377627976568607109 437622445805245606613833)
                  ·
                    rfl

theorem cell21_1917600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 4].length) (baseStart_1917600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1917600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1917600 prefixEnd_1917600 := by exact prefixLift 1917600
  have htrace : WordTrace (prefixWord ++ tailWord_1917600) baseStart_1917600 baseEnd_1917600 := by
    simpa [prefixWord, tailWord_1917600, baseEnd_1917600] using wordTrace_append hprefix tailTrace_1917600
  have hstable : (prefixWord ++ tailWord_1917600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917600).length < 2 ^ (prefixWord ++ tailWord_1917600).sum := by decide
  have hdescent : baseEnd_1917600 < baseStart_1917600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917617 : List Nat := [1, 2, 2, 6, 1, 1, 3, 1, 4]
def baseStart_1917617 : Nat := 118140960795 + 1917617 * 2 ^ 59
def prefixEnd_1917617 : Nat := 4983230072969 + 3 ^ 40 * 1917617 * 2
def baseEnd_1917617 : Nat := 437626325436857354830465

theorem tailTrace_1917617 : CollatzResearch.WordTrace tailWord_1917617 prefixEnd_1917617 437626325436857354830465 := by
  unfold tailWord_1917617
  simp only [CollatzResearch.WordTrace]
  refine ⟨69941237893808586754871105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46627491929205724503247403 69941237893808586754871105)
  ·
    refine ⟨52455928420356440066153329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69941237893808586754871105 52455928420356440066153329)
    ·
      refine ⟨39341946315267330049614997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52455928420356440066153329 39341946315267330049614997)
      ·
        refine ⟨1844153733528156096075703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39341946315267330049614997 1844153733528156096075703)
        ·
          refine ⟨2766230600292234144113555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1844153733528156096075703 2766230600292234144113555)
          ·
            refine ⟨4149345900438351216170333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2766230600292234144113555 4149345900438351216170333)
            ·
              refine ⟨1556004712664381706063875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4149345900438351216170333 1556004712664381706063875)
              ·
                refine ⟨2334007068996572559095813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1556004712664381706063875 2334007068996572559095813)
                ·
                  refine ⟨437626325436857354830465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2334007068996572559095813 437626325436857354830465)
                  ·
                    rfl

theorem cell21_1917617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 4].length) (baseStart_1917617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1917617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1917617 prefixEnd_1917617 := by exact prefixLift 1917617
  have htrace : WordTrace (prefixWord ++ tailWord_1917617) baseStart_1917617 baseEnd_1917617 := by
    simpa [prefixWord, tailWord_1917617, baseEnd_1917617] using wordTrace_append hprefix tailTrace_1917617
  have hstable : (prefixWord ++ tailWord_1917617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917617).length < 2 ^ (prefixWord ++ tailWord_1917617).sum := by decide
  have hdescent : baseEnd_1917617 < baseStart_1917617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917642 : List Nat := [3, 1, 2, 1, 4, 1, 1, 2, 6]
def baseStart_1917642 : Nat := 118140960795 + 1917642 * 2 ^ 59
def prefixEnd_1917642 : Nat := 4983230072969 + 3 ^ 40 * 1917642 * 2
def baseEnd_1917642 : Nat := 437632030777462866913747

theorem tailTrace_1917642 : CollatzResearch.WordTrace tailWord_1917642 prefixEnd_1917642 437632030777462866913747 := by
  unfold tailWord_1917642
  simp only [CollatzResearch.WordTrace]
  refine ⟨17485537429679504006132795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46628099812478677349687453 17485537429679504006132795)
  ·
    refine ⟨26228306144519256009199193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17485537429679504006132795 26228306144519256009199193)
    ·
      refine ⟨19671229608389442006899395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26228306144519256009199193 19671229608389442006899395)
      ·
        refine ⟨29506844412584163010349093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19671229608389442006899395 29506844412584163010349093)
        ·
          refine ⟨5532533327359530564440455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29506844412584163010349093 5532533327359530564440455)
          ·
            refine ⟨8298799991039295846660683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5532533327359530564440455 8298799991039295846660683)
            ·
              refine ⟨12448199986558943769991025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8298799991039295846660683 12448199986558943769991025)
              ·
                refine ⟨9336149989919207827493269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12448199986558943769991025 9336149989919207827493269)
                ·
                  refine ⟨437632030777462866913747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9336149989919207827493269 437632030777462866913747)
                  ·
                    rfl

theorem cell21_1917642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_1917642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1917642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1917642 prefixEnd_1917642 := by exact prefixLift 1917642
  have htrace : WordTrace (prefixWord ++ tailWord_1917642) baseStart_1917642 baseEnd_1917642 := by
    simpa [prefixWord, tailWord_1917642, baseEnd_1917642] using wordTrace_append hprefix tailTrace_1917642
  have hstable : (prefixWord ++ tailWord_1917642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917642).length < 2 ^ (prefixWord ++ tailWord_1917642).sum := by decide
  have hdescent : baseEnd_1917642 < baseStart_1917642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917656 : List Nat := [2, 1, 2, 2, 3, 2, 9]
def baseStart_1917656 : Nat := 118140960795 + 1917656 * 2 ^ 59
def prefixEnd_1917656 : Nat := 4983230072969 + 3 ^ 40 * 1917656 * 2
def baseEnd_1917656 : Nat := 48626136196466883742265

theorem tailTrace_1917656 : CollatzResearch.WordTrace tailWord_1917656 prefixEnd_1917656 48626136196466883742265 := by
  unfold tailWord_1917656
  simp only [CollatzResearch.WordTrace]
  refine ⟨34971330170333648207770411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46628440227111530943693881 34971330170333648207770411)
  ·
    refine ⟨52456995255500472311655617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34971330170333648207770411 52456995255500472311655617)
    ·
      refine ⟨39342746441625354233741713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52456995255500472311655617 39342746441625354233741713)
      ·
        refine ⟨29507059831219015675306285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39342746441625354233741713 29507059831219015675306285)
        ·
          refine ⟨11065147436707130878239857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29507059831219015675306285 11065147436707130878239857)
          ·
            refine ⟨8298860577530348158679893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11065147436707130878239857 8298860577530348158679893)
            ·
              refine ⟨48626136196466883742265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8298860577530348158679893 48626136196466883742265)
              ·
                rfl

theorem cell21_1917656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 9].length) (baseStart_1917656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1917656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1917656 prefixEnd_1917656 := by exact prefixLift 1917656
  have htrace : WordTrace (prefixWord ++ tailWord_1917656) baseStart_1917656 baseEnd_1917656 := by
    simpa [prefixWord, tailWord_1917656, baseEnd_1917656] using wordTrace_append hprefix tailTrace_1917656
  have hstable : (prefixWord ++ tailWord_1917656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917656).length < 2 ^ (prefixWord ++ tailWord_1917656).sum := by decide
  have hdescent : baseEnd_1917656 < baseStart_1917656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917701 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 8]
def baseStart_1917701 : Nat := 118140960795 + 1917701 * 2 ^ 59
def prefixEnd_1917701 : Nat := 4983230072969 + 3 ^ 40 * 1917701 * 2
def baseEnd_1917701 : Nat := 437645495381291875430293

theorem tailTrace_1917701 : CollatzResearch.WordTrace tailWord_1917701 prefixEnd_1917701 437645495381291875430293 := by
  unfold tailWord_1917701
  simp only [CollatzResearch.WordTrace]
  refine ⟨69944301625504269100928957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46629534417002846067285971 69944301625504269100928957)
  ·
    refine ⟨26229113109564100912848359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69944301625504269100928957 26229113109564100912848359)
    ·
      refine ⟨39343669664346151369272539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26229113109564100912848359 39343669664346151369272539)
      ·
        refine ⟨59015504496519227053908809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39343669664346151369272539 59015504496519227053908809)
        ·
          refine ⟨44261628372389420290431607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59015504496519227053908809 44261628372389420290431607)
          ·
            refine ⟨66392442558584130435647411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44261628372389420290431607 66392442558584130435647411)
            ·
              refine ⟨99588663837876195653471117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66392442558584130435647411 99588663837876195653471117)
              ·
                refine ⟨37345748939203573370051669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99588663837876195653471117 37345748939203573370051669)
                ·
                  refine ⟨437645495381291875430293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37345748939203573370051669 437645495381291875430293)
                  ·
                    rfl

theorem cell21_1917701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_1917701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1917701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1917701 prefixEnd_1917701 := by exact prefixLift 1917701
  have htrace : WordTrace (prefixWord ++ tailWord_1917701) baseStart_1917701 baseEnd_1917701 := by
    simpa [prefixWord, tailWord_1917701, baseEnd_1917701] using wordTrace_append hprefix tailTrace_1917701
  have hstable : (prefixWord ++ tailWord_1917701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917701).length < 2 ^ (prefixWord ++ tailWord_1917701).sum := by decide
  have hdescent : baseEnd_1917701 < baseStart_1917701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917814 : List Nat := [5, 1, 1, 3, 1, 1, 3, 3, 3]
def baseStart_1917814 : Nat := 118140960795 + 1917814 * 2 ^ 59
def prefixEnd_1917814 : Nat := 4983230072969 + 3 ^ 40 * 1917814 * 2
def baseEnd_1917814 : Nat := 437671283520828790046729

theorem tailTrace_1917814 : CollatzResearch.WordTrace tailWord_1917814 prefixEnd_1917814 437671283520828790046729 := by
  unfold tailWord_1917814
  simp only [CollatzResearch.WordTrace]
  refine ⟨4371776442130930587487031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46632282049396592933194997 4371776442130930587487031)
  ·
    refine ⟨6557664663196395881230547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4371776442130930587487031 6557664663196395881230547)
    ·
      refine ⟨9836496994794593821845821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6557664663196395881230547 9836496994794593821845821)
      ·
        refine ⟨3688686373047972683192183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9836496994794593821845821 3688686373047972683192183)
        ·
          refine ⟨5533029559571959024788275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3688686373047972683192183 5533029559571959024788275)
          ·
            refine ⟨8299544339357938537182413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5533029559571959024788275 8299544339357938537182413)
            ·
              refine ⟨3112329127259226951443405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8299544339357938537182413 3112329127259226951443405)
              ·
                refine ⟨1167123422722210106791277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3112329127259226951443405 1167123422722210106791277)
                ·
                  refine ⟨437671283520828790046729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1167123422722210106791277 437671283520828790046729)
                  ·
                    rfl

theorem cell21_1917814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_1917814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1917814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1917814 prefixEnd_1917814 := by exact prefixLift 1917814
  have htrace : WordTrace (prefixWord ++ tailWord_1917814) baseStart_1917814 baseEnd_1917814 := by
    simpa [prefixWord, tailWord_1917814, baseEnd_1917814] using wordTrace_append hprefix tailTrace_1917814
  have hstable : (prefixWord ++ tailWord_1917814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917814).length < 2 ^ (prefixWord ++ tailWord_1917814).sum := by decide
  have hdescent : baseEnd_1917814 < baseStart_1917814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917842 : List Nat := [3, 2, 3, 2, 2, 1, 2, 6]
def baseStart_1917842 : Nat := 118140960795 + 1917842 * 2 ^ 59
def prefixEnd_1917842 : Nat := 4983230072969 + 3 ^ 40 * 1917842 * 2
def baseEnd_1917842 : Nat := 145892557834102321193335

theorem tailTrace_1917842 : CollatzResearch.WordTrace tailWord_1917842 prefixEnd_1917842 145892557834102321193335 := by
  unfold tailWord_1917842
  simp only [CollatzResearch.WordTrace]
  refine ⟨17487361079498362545452945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46632962878662300121207853 17487361079498362545452945)
  ·
    refine ⟨13115520809623771909089709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17487361079498362545452945 13115520809623771909089709)
    ·
      refine ⟨4918320303608914465908641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13115520809623771909089709 4918320303608914465908641)
      ·
        refine ⟨3688740227706685849431481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4918320303608914465908641 3688740227706685849431481)
        ·
          refine ⟨2766555170780014387073611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3688740227706685849431481 2766555170780014387073611)
          ·
            refine ⟨4149832756170021580610417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2766555170780014387073611 4149832756170021580610417)
            ·
              refine ⟨3112374567127516185457813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4149832756170021580610417 3112374567127516185457813)
              ·
                refine ⟨145892557834102321193335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3112374567127516185457813 145892557834102321193335)
                ·
                  rfl

theorem cell21_1917842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 6].length) (baseStart_1917842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1917842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1917842 prefixEnd_1917842 := by exact prefixLift 1917842
  have htrace : WordTrace (prefixWord ++ tailWord_1917842) baseStart_1917842 baseEnd_1917842 := by
    simpa [prefixWord, tailWord_1917842, baseEnd_1917842] using wordTrace_append hprefix tailTrace_1917842
  have hstable : (prefixWord ++ tailWord_1917842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917842).length < 2 ^ (prefixWord ++ tailWord_1917842).sum := by decide
  have hdescent : baseEnd_1917842 < baseStart_1917842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917963 : List Nat := [1, 1, 1, 1, 6, 3, 3, 1, 4]
def baseStart_1917963 : Nat := 118140960795 + 1917963 * 2 ^ 59
def prefixEnd_1917963 : Nat := 4983230072969 + 3 ^ 40 * 1917963 * 2
def baseEnd_1917963 : Nat := 437705287350837642063091

theorem tailTrace_1917963 : CollatzResearch.WordTrace tailWord_1917963 prefixEnd_1917963 437705287350837642063091 := by
  unfold tailWord_1917963
  simp only [CollatzResearch.WordTrace]
  refine ⟨69953857550555087846966543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46635905033703391897977695 69953857550555087846966543)
  ·
    refine ⟨104930786325832631770449815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69953857550555087846966543 104930786325832631770449815)
    ·
      refine ⟨157396179488748947655674723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104930786325832631770449815 157396179488748947655674723)
      ·
        refine ⟨236094269233123421483512085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157396179488748947655674723 236094269233123421483512085)
        ·
          refine ⟨11066918870302660382039629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 236094269233123421483512085 11066918870302660382039629)
          ·
            refine ⟨4150094576363497643264861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11066918870302660382039629 4150094576363497643264861)
            ·
              refine ⟨1556285466136311616224323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4150094576363497643264861 1556285466136311616224323)
              ·
                refine ⟨2334428199204467424336485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1556285466136311616224323 2334428199204467424336485)
                ·
                  refine ⟨437705287350837642063091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2334428199204467424336485 437705287350837642063091)
                  ·
                    rfl

theorem cell21_1917963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 4].length) (baseStart_1917963 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1917963 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1917963 prefixEnd_1917963 := by exact prefixLift 1917963
  have htrace : WordTrace (prefixWord ++ tailWord_1917963) baseStart_1917963 baseEnd_1917963 := by
    simpa [prefixWord, tailWord_1917963, baseEnd_1917963] using wordTrace_append hprefix tailTrace_1917963
  have hstable : (prefixWord ++ tailWord_1917963).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917963).length < 2 ^ (prefixWord ++ tailWord_1917963).sum := by decide
  have hdescent : baseEnd_1917963 < baseStart_1917963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917994 : List Nat := [3, 1, 4, 1, 4, 1, 7]
def baseStart_1917994 : Nat := 118140960795 + 1917994 * 2 ^ 59
def prefixEnd_1917994 : Nat := 4983230072969 + 3 ^ 40 * 1917994 * 2
def baseEnd_1917994 : Nat := 48634706885909830782929

theorem tailTrace_1917994 : CollatzResearch.WordTrace tailWord_1917994 prefixEnd_1917994 48634706885909830782929 := by
  unfold tailWord_1917994
  simp only [CollatzResearch.WordTrace]
  refine ⟨17488747053360695035336259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46636658808961853427563357 17488747053360695035336259)
  ·
    refine ⟨26233120580041042553004389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17488747053360695035336259 26233120580041042553004389)
    ·
      refine ⟨4918710108757695478688323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26233120580041042553004389 4918710108757695478688323)
      ·
        refine ⟨7378065163136543218032485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4918710108757695478688323 7378065163136543218032485)
        ·
          refine ⟨1383387218088101853381091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7378065163136543218032485 1383387218088101853381091)
          ·
            refine ⟨2075080827132152780071637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1383387218088101853381091 2075080827132152780071637)
            ·
              refine ⟨48634706885909830782929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2075080827132152780071637 48634706885909830782929)
              ·
                rfl

theorem cell21_1917994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 7].length) (baseStart_1917994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1917994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1917994 prefixEnd_1917994 := by exact prefixLift 1917994
  have htrace : WordTrace (prefixWord ++ tailWord_1917994) baseStart_1917994 baseEnd_1917994 := by
    simpa [prefixWord, tailWord_1917994, baseEnd_1917994] using wordTrace_append hprefix tailTrace_1917994
  have hstable : (prefixWord ++ tailWord_1917994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917994).length < 2 ^ (prefixWord ++ tailWord_1917994).sum := by decide
  have hdescent : baseEnd_1917994 < baseStart_1917994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918008 : List Nat := [2, 1, 2, 1, 5, 3, 1, 1, 5]
def baseStart_1918008 : Nat := 118140960795 + 1918008 * 2 ^ 59
def prefixEnd_1918008 : Nat := 4983230072969 + 3 ^ 40 * 1918008 * 2
def baseEnd_1918008 : Nat := 437715556963927563812999

theorem tailTrace_1918008 : CollatzResearch.WordTrace tailWord_1918008 prefixEnd_1918008 437715556963927563812999 := by
  unfold tailWord_1918008
  simp only [CollatzResearch.WordTrace]
  refine ⟨34977749417696030266177339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46636999223594707021569785 34977749417696030266177339)
  ·
    refine ⟨52466624126544045399266009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34977749417696030266177339 52466624126544045399266009)
    ·
      refine ⟨39349968094908034049449507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52466624126544045399266009 39349968094908034049449507)
      ·
        refine ⟨59024952142362051074174261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39349968094908034049449507 59024952142362051074174261)
        ·
          refine ⟨5533589263346442288203837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59024952142362051074174261 5533589263346442288203837)
          ·
            refine ⟨2075095973754915858076439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5533589263346442288203837 2075095973754915858076439)
            ·
              refine ⟨3112643960632373787114659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2075095973754915858076439 3112643960632373787114659)
              ·
                refine ⟨4668965940948560680671989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3112643960632373787114659 4668965940948560680671989)
                ·
                  refine ⟨437715556963927563812999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4668965940948560680671989 437715556963927563812999)
                  ·
                    rfl

theorem cell21_1918008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 5].length) (baseStart_1918008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1918008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1918008 prefixEnd_1918008 := by exact prefixLift 1918008
  have htrace : WordTrace (prefixWord ++ tailWord_1918008) baseStart_1918008 baseEnd_1918008 := by
    simpa [prefixWord, tailWord_1918008, baseEnd_1918008] using wordTrace_append hprefix tailTrace_1918008
  have hstable : (prefixWord ++ tailWord_1918008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918008).length < 2 ^ (prefixWord ++ tailWord_1918008).sum := by decide
  have hdescent : baseEnd_1918008 < baseStart_1918008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918036 : List Nat := [2, 4, 1, 1, 1, 1, 4, 7]
def baseStart_1918036 : Nat := 118140960795 + 1918036 * 2 ^ 59
def prefixEnd_1918036 : Nat := 4983230072969 + 3 ^ 40 * 1918036 * 2
def baseEnd_1918036 : Nat := 145907315648468579115425

theorem tailTrace_1918036 : CollatzResearch.WordTrace tailWord_1918036 prefixEnd_1918036 145907315648468579115425 := by
  unfold tailWord_1918036
  simp only [CollatzResearch.WordTrace]
  refine ⟨34978260039645310657186981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46637680052860414209582641 34978260039645310657186981)
  ·
    refine ⟨6558423757433495748222559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34978260039645310657186981 6558423757433495748222559)
    ·
      refine ⟨9837635636150243622333839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6558423757433495748222559 9837635636150243622333839)
      ·
        refine ⟨14756453454225365433500759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9837635636150243622333839 14756453454225365433500759)
        ·
          refine ⟨22134680181338048150251139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14756453454225365433500759 22134680181338048150251139)
          ·
            refine ⟨33202020272007072225376709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22134680181338048150251139 33202020272007072225376709)
            ·
              refine ⟨6225378801001326042258133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33202020272007072225376709 6225378801001326042258133)
              ·
                refine ⟨145907315648468579115425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6225378801001326042258133 145907315648468579115425)
                ·
                  rfl

theorem cell21_1918036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 7].length) (baseStart_1918036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1918036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1918036 prefixEnd_1918036 := by exact prefixLift 1918036
  have htrace : WordTrace (prefixWord ++ tailWord_1918036) baseStart_1918036 baseEnd_1918036 := by
    simpa [prefixWord, tailWord_1918036, baseEnd_1918036] using wordTrace_append hprefix tailTrace_1918036
  have hstable : (prefixWord ++ tailWord_1918036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918036).length < 2 ^ (prefixWord ++ tailWord_1918036).sum := by decide
  have hdescent : baseEnd_1918036 < baseStart_1918036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918056 : List Nat := [2, 1, 4, 4, 1, 1, 2, 2, 4]
def baseStart_1918056 : Nat := 118140960795 + 1918056 * 2 ^ 59
def prefixEnd_1918056 : Nat := 4983230072969 + 3 ^ 40 * 1918056 * 2
def baseEnd_1918056 : Nat := 437726511217890147012901

theorem tailTrace_1918056 : CollatzResearch.WordTrace tailWord_1918056 prefixEnd_1918056 437726511217890147012901 := by
  unfold tailWord_1918056
  simp only [CollatzResearch.WordTrace]
  refine ⟨34978624769609082365051011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46638166359478776486734681 34978624769609082365051011)
  ·
    refine ⟨52467937154413623547576517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34978624769609082365051011 52467937154413623547576517)
    ·
      refine ⟨9837738216452554415170597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52467937154413623547576517 9837738216452554415170597)
      ·
        refine ⟨1844575915584853952844487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9837738216452554415170597 1844575915584853952844487)
        ·
          refine ⟨2766863873377280929266731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1844575915584853952844487 2766863873377280929266731)
          ·
            refine ⟨4150295810065921393900097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2766863873377280929266731 4150295810065921393900097)
            ·
              refine ⟨3112721857549441045425073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4150295810065921393900097 3112721857549441045425073)
              ·
                refine ⟨2334541393162080784068805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3112721857549441045425073 2334541393162080784068805)
                ·
                  refine ⟨437726511217890147012901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2334541393162080784068805 437726511217890147012901)
                  ·
                    rfl

theorem cell21_1918056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 4].length) (baseStart_1918056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1918056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1918056 prefixEnd_1918056 := by exact prefixLift 1918056
  have htrace : WordTrace (prefixWord ++ tailWord_1918056) baseStart_1918056 baseEnd_1918056 := by
    simpa [prefixWord, tailWord_1918056, baseEnd_1918056] using wordTrace_append hprefix tailTrace_1918056
  have hstable : (prefixWord ++ tailWord_1918056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918056).length < 2 ^ (prefixWord ++ tailWord_1918056).sum := by decide
  have hdescent : baseEnd_1918056 < baseStart_1918056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918177 : List Nat := [1, 2, 3, 1, 3, 3, 3, 2, 3]
def baseStart_1918177 : Nat := 118140960795 + 1918177 * 2 ^ 59
def prefixEnd_1918177 : Nat := 4983230072969 + 3 ^ 40 * 1918177 * 2
def baseEnd_1918177 : Nat := 437754125066420825495987

theorem tailTrace_1918177 : CollatzResearch.WordTrace tailWord_1918177 prefixEnd_1918177 437754125066420825495987 := by
  unfold tailWord_1918177
  simp only [CollatzResearch.WordTrace]
  refine ⟨69961662771779802395256785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46641108514519868263504523 69961662771779802395256785)
  ·
    refine ⟨52471247078834851796442589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69961662771779802395256785 52471247078834851796442589)
    ·
      refine ⟨19676717654563069423665971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52471247078834851796442589 19676717654563069423665971)
      ·
        refine ⟨29515076481844604135498957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19676717654563069423665971 29515076481844604135498957)
        ·
          refine ⟨11068153680691726550812109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29515076481844604135498957 11068153680691726550812109)
          ·
            refine ⟨4150557630259397456554541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11068153680691726550812109 4150557630259397456554541)
            ·
              refine ⟨1556459111347274046207953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4150557630259397456554541 1556459111347274046207953)
              ·
                refine ⟨1167344333510455534655965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1556459111347274046207953 1167344333510455534655965)
                ·
                  refine ⟨437754125066420825495987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1167344333510455534655965 437754125066420825495987)
                  ·
                    rfl

theorem cell21_1918177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2, 3].length) (baseStart_1918177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1918177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1918177 prefixEnd_1918177 := by exact prefixLift 1918177
  have htrace : WordTrace (prefixWord ++ tailWord_1918177) baseStart_1918177 baseEnd_1918177 := by
    simpa [prefixWord, tailWord_1918177, baseEnd_1918177] using wordTrace_append hprefix tailTrace_1918177
  have hstable : (prefixWord ++ tailWord_1918177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918177).length < 2 ^ (prefixWord ++ tailWord_1918177).sum := by decide
  have hdescent : baseEnd_1918177 < baseStart_1918177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918188 : List Nat := [2, 2, 1, 1, 2, 5, 2, 6]
def baseStart_1918188 : Nat := 118140960795 + 1918188 * 2 ^ 59
def prefixEnd_1918188 : Nat := 4983230072969 + 3 ^ 40 * 1918188 * 2
def baseEnd_1918188 : Nat := 145918878472095750270877

theorem tailTrace_1918188 : CollatzResearch.WordTrace tailWord_1918188 prefixEnd_1918188 145918878472095750270877 := by
  unfold tailWord_1918188
  simp only [CollatzResearch.WordTrace]
  refine ⟨34981031987369975636953609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46641375983159967515938145 34981031987369975636953609)
  ·
    refine ⟨26235773990527481727715207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34981031987369975636953609 26235773990527481727715207)
    ·
      refine ⟨39353660985791222591572811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26235773990527481727715207 39353660985791222591572811)
      ·
        refine ⟨59030491478686833887359217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39353660985791222591572811 59030491478686833887359217)
        ·
          refine ⟨44272868609015125415519413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59030491478686833887359217 44272868609015125415519413)
          ·
            refine ⟨4150581432095168007704945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44272868609015125415519413 4150581432095168007704945)
            ·
              refine ⟨3112936074071376005778709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4150581432095168007704945 3112936074071376005778709)
              ·
                refine ⟨145918878472095750270877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3112936074071376005778709 145918878472095750270877)
                ·
                  rfl

theorem cell21_1918188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 6].length) (baseStart_1918188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1918188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1918188 prefixEnd_1918188 := by exact prefixLift 1918188
  have htrace : WordTrace (prefixWord ++ tailWord_1918188) baseStart_1918188 baseEnd_1918188 := by
    simpa [prefixWord, tailWord_1918188, baseEnd_1918188] using wordTrace_append hprefix tailTrace_1918188
  have hstable : (prefixWord ++ tailWord_1918188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918188).length < 2 ^ (prefixWord ++ tailWord_1918188).sum := by decide
  have hdescent : baseEnd_1918188 < baseStart_1918188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918202 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 7]
def baseStart_1918202 : Nat := 118140960795 + 1918202 * 2 ^ 59
def prefixEnd_1918202 : Nat := 4983230072969 + 3 ^ 40 * 1918202 * 2
def baseEnd_1918202 : Nat := 437759830407026337579269

theorem tailTrace_1918202 : CollatzResearch.WordTrace tailWord_1918202 prefixEnd_1918202 437759830407026337579269 := by
  unfold tailWord_1918202
  simp only [CollatzResearch.WordTrace]
  refine ⟨17490643649172307916229215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46641716397792821109944573 17490643649172307916229215)
  ·
    refine ⟨26235965473758461874343823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17490643649172307916229215 26235965473758461874343823)
    ·
      refine ⟨39353948210637692811515735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26235965473758461874343823 39353948210637692811515735)
      ·
        refine ⟨59030922315956539217273603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39353948210637692811515735 59030922315956539217273603)
        ·
          refine ⟨88546383473934808825910405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59030922315956539217273603 88546383473934808825910405)
          ·
            refine ⟨16602446901362776654858201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88546383473934808825910405 16602446901362776654858201)
            ·
              refine ⟨12451835176022082491143651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16602446901362776654858201 12451835176022082491143651)
              ·
                refine ⟨18677752764033123736715477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12451835176022082491143651 18677752764033123736715477)
                ·
                  refine ⟨437759830407026337579269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18677752764033123736715477 437759830407026337579269)
                  ·
                    rfl

theorem cell21_1918202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_1918202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1918202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1918202 prefixEnd_1918202 := by exact prefixLift 1918202
  have htrace : WordTrace (prefixWord ++ tailWord_1918202) baseStart_1918202 baseEnd_1918202 := by
    simpa [prefixWord, tailWord_1918202, baseEnd_1918202] using wordTrace_append hprefix tailTrace_1918202
  have hstable : (prefixWord ++ tailWord_1918202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918202).length < 2 ^ (prefixWord ++ tailWord_1918202).sum := by decide
  have hdescent : baseEnd_1918202 < baseStart_1918202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918295 : List Nat := [1, 1, 3, 2, 3, 3, 2, 1, 5]
def baseStart_1918295 : Nat := 118140960795 + 1918295 * 2 ^ 59
def prefixEnd_1918295 : Nat := 4983230072969 + 3 ^ 40 * 1918295 * 2
def baseEnd_1918295 : Nat := 437781054274078842529079

theorem tailTrace_1918295 : CollatzResearch.WordTrace tailWord_1918295 prefixEnd_1918295 437781054274078842529079 := by
  unfold tailWord_1918295
  simp only [CollatzResearch.WordTrace]
  refine ⟨69965966585352308548052339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46643977723568205698701559 69965966585352308548052339)
  ·
    refine ⟨104948949878028462822078509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69965966585352308548052339 104948949878028462822078509)
    ·
      refine ⟨39355856204260673558279441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104948949878028462822078509 39355856204260673558279441)
      ·
        refine ⟨29516892153195505168709581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39355856204260673558279441 29516892153195505168709581)
        ·
          refine ⟨11068834557448314438266093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29516892153195505168709581 11068834557448314438266093)
          ·
            refine ⟨4150812959043117914349785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11068834557448314438266093 4150812959043117914349785)
            ·
              refine ⟨3113109719282338435762339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4150812959043117914349785 3113109719282338435762339)
              ·
                refine ⟨4669664578923507653643509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3113109719282338435762339 4669664578923507653643509)
                ·
                  refine ⟨437781054274078842529079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4669664578923507653643509 437781054274078842529079)
                  ·
                    rfl

theorem cell21_1918295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 5].length) (baseStart_1918295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1918295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1918295 prefixEnd_1918295 := by exact prefixLift 1918295
  have htrace : WordTrace (prefixWord ++ tailWord_1918295) baseStart_1918295 baseEnd_1918295 := by
    simpa [prefixWord, tailWord_1918295, baseEnd_1918295] using wordTrace_append hprefix tailTrace_1918295
  have hstable : (prefixWord ++ tailWord_1918295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918295).length < 2 ^ (prefixWord ++ tailWord_1918295).sum := by decide
  have hdescent : baseEnd_1918295 < baseStart_1918295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918340 : List Nat := [2, 3, 2, 1, 1, 5, 7]
def baseStart_1918340 : Nat := 118140960795 + 1918340 * 2 ^ 59
def prefixEnd_1918340 : Nat := 4983230072969 + 3 ^ 40 * 1918340 * 2
def baseEnd_1918340 : Nat := 48643480431907640475443

theorem tailTrace_1918340 : CollatzResearch.WordTrace tailWord_1918340 prefixEnd_1918340 48643480431907640475443 := by
  unfold tailWord_1918340
  simp only [CollatzResearch.WordTrace]
  refine ⟨34983803935094640616720237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46645071913459520822293649 34983803935094640616720237)
  ·
    refine ⟨13118926475660490231270089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34983803935094640616720237 13118926475660490231270089)
    ·
      refine ⟨9839194856745367673452567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13118926475660490231270089 9839194856745367673452567)
      ·
        refine ⟨14758792285118051510178851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9839194856745367673452567 14758792285118051510178851)
        ·
          refine ⟨22138188427677077265268277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14758792285118051510178851 22138188427677077265268277)
          ·
            refine ⟨2075455165094725993618901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22138188427677077265268277 2075455165094725993618901)
            ·
              refine ⟨48643480431907640475443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2075455165094725993618901 48643480431907640475443)
              ·
                rfl

theorem cell21_1918340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 7].length) (baseStart_1918340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1918340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1918340 prefixEnd_1918340 := by exact prefixLift 1918340
  have htrace : WordTrace (prefixWord ++ tailWord_1918340) baseStart_1918340 baseEnd_1918340 := by
    simpa [prefixWord, tailWord_1918340, baseEnd_1918340] using wordTrace_append hprefix tailTrace_1918340
  have hstable : (prefixWord ++ tailWord_1918340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918340).length < 2 ^ (prefixWord ++ tailWord_1918340).sum := by decide
  have hdescent : baseEnd_1918340 < baseStart_1918340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918360 : List Nat := [2, 1, 2, 5, 2, 2, 2, 1, 4]
def baseStart_1918360 : Nat := 118140960795 + 1918360 * 2 ^ 59
def prefixEnd_1918360 : Nat := 4983230072969 + 3 ^ 40 * 1918360 * 2
def baseEnd_1918360 : Nat := 437795888159653173945613

theorem tailTrace_1918360 : CollatzResearch.WordTrace tailWord_1918360 prefixEnd_1918360 437795888159653173945613 := by
  unfold tailWord_1918360
  simp only [CollatzResearch.WordTrace]
  refine ⟨34984168665058412324584267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46645558220077883099445689 34984168665058412324584267)
  ·
    refine ⟨52476252997587618486876401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34984168665058412324584267 52476252997587618486876401)
    ·
      refine ⟨39357189748190713865157301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52476252997587618486876401 39357189748190713865157301)
      ·
        refine ⟨3689736538892879424858497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39357189748190713865157301 3689736538892879424858497)
        ·
          refine ⟨2767302404169659568643873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3689736538892879424858497 2767302404169659568643873)
          ·
            refine ⟨2075476803127244676482905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2767302404169659568643873 2075476803127244676482905)
            ·
              refine ⟨1556607602345433507362179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2075476803127244676482905 1556607602345433507362179)
              ·
                refine ⟨2334911403518150261043269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1556607602345433507362179 2334911403518150261043269)
                ·
                  refine ⟨437795888159653173945613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2334911403518150261043269 437795888159653173945613)
                  ·
                    rfl

theorem cell21_1918360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 4].length) (baseStart_1918360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1918360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1918360 prefixEnd_1918360 := by exact prefixLift 1918360
  have htrace : WordTrace (prefixWord ++ tailWord_1918360) baseStart_1918360 baseEnd_1918360 := by
    simpa [prefixWord, tailWord_1918360, baseEnd_1918360] using wordTrace_append hprefix tailTrace_1918360
  have hstable : (prefixWord ++ tailWord_1918360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918360).length < 2 ^ (prefixWord ++ tailWord_1918360).sum := by decide
  have hdescent : baseEnd_1918360 < baseStart_1918360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918447 : List Nat := [1, 1, 2, 1, 4, 1, 3, 5, 3]
def baseStart_1918447 : Nat := 118140960795 + 1918447 * 2 ^ 59
def prefixEnd_1918447 : Nat := 4983230072969 + 3 ^ 40 * 1918447 * 2
def baseEnd_1918447 : Nat := 437815742744960355995435

theorem tailTrace_1918447 : CollatzResearch.WordTrace tailWord_1918447 prefixEnd_1918447 437815742744960355995435 := by
  unfold tailWord_1918447
  simp only [CollatzResearch.WordTrace]
  refine ⟨69971510480801638507585595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46647673653867759005057063 69971510480801638507585595)
  ·
    refine ⟨104957265721202457761378393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69971510480801638507585595 104957265721202457761378393)
    ·
      refine ⟨78717949290901843321033795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104957265721202457761378393 78717949290901843321033795)
      ·
        refine ⟨118076923936352764981550693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78717949290901843321033795 118076923936352764981550693)
        ·
          refine ⟨22139423238066143434040755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118076923936352764981550693 22139423238066143434040755)
          ·
            refine ⟨33209134857099215151061133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22139423238066143434040755 33209134857099215151061133)
            ·
              refine ⟨12453425571412205681647925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33209134857099215151061133 12453425571412205681647925)
              ·
                refine ⟨1167508647319894282654493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12453425571412205681647925 1167508647319894282654493)
                ·
                  refine ⟨437815742744960355995435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1167508647319894282654493 437815742744960355995435)
                  ·
                    rfl

theorem cell21_1918447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5, 3].length) (baseStart_1918447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1918447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1918447 prefixEnd_1918447 := by exact prefixLift 1918447
  have htrace : WordTrace (prefixWord ++ tailWord_1918447) baseStart_1918447 baseEnd_1918447 := by
    simpa [prefixWord, tailWord_1918447, baseEnd_1918447] using wordTrace_append hprefix tailTrace_1918447
  have hstable : (prefixWord ++ tailWord_1918447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918447).length < 2 ^ (prefixWord ++ tailWord_1918447).sum := by decide
  have hdescent : baseEnd_1918447 < baseStart_1918447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918461 : List Nat := [1, 4, 1, 1, 1, 5, 1, 1, 6]
def baseStart_1918461 : Nat := 118140960795 + 1918461 * 2 ^ 59
def prefixEnd_1918461 : Nat := 4983230072969 + 3 ^ 40 * 1918461 * 2
def baseEnd_1918461 : Nat := 437818937735699442762073

theorem tailTrace_1918461 : CollatzResearch.WordTrace tailWord_1918461 prefixEnd_1918461 437818937735699442762073 := by
  unfold tailWord_1918461
  simp only [CollatzResearch.WordTrace]
  refine ⟨69972021102750918898595237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46648014068500612599063491 69972021102750918898595237)
  ·
    refine ⟨13119753956765797293486607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69972021102750918898595237 13119753956765797293486607)
    ·
      refine ⟨19679630935148695940229911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13119753956765797293486607 19679630935148695940229911)
      ·
        refine ⟨29519446402723043910344867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19679630935148695940229911 29519446402723043910344867)
        ·
          refine ⟨44279169604084565865517301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29519446402723043910344867 44279169604084565865517301)
          ·
            refine ⟨4151172150382928049892247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44279169604084565865517301 4151172150382928049892247)
            ·
              refine ⟨6226758225574392074838371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4151172150382928049892247 6226758225574392074838371)
              ·
                refine ⟨9340137338361588112257557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6226758225574392074838371 9340137338361588112257557)
                ·
                  refine ⟨437818937735699442762073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9340137338361588112257557 437818937735699442762073)
                  ·
                    rfl

theorem cell21_1918461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_1918461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1918461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1918461 prefixEnd_1918461 := by exact prefixLift 1918461
  have htrace : WordTrace (prefixWord ++ tailWord_1918461) baseStart_1918461 baseEnd_1918461 := by
    simpa [prefixWord, tailWord_1918461, baseEnd_1918461] using wordTrace_append hprefix tailTrace_1918461
  have hstable : (prefixWord ++ tailWord_1918461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918461).length < 2 ^ (prefixWord ++ tailWord_1918461).sum := by decide
  have hdescent : baseEnd_1918461 < baseStart_1918461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918470 : List Nat := [6, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_1918470 : Nat := 118140960795 + 1918470 * 2 ^ 59
def prefixEnd_1918470 : Nat := 4983230072969 + 3 ^ 40 * 1918470 * 2
def baseEnd_1918470 : Nat := 437820991658317427112055

theorem tailTrace_1918470 : CollatzResearch.WordTrace tailWord_1918470 prefixEnd_1918470 437820991658317427112055 := by
  unfold tailWord_1918470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2186635917491197294864777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46648232906478875623781909 2186635917491197294864777)
  ·
    refine ⟨1639976938118397971148583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2186635917491197294864777 1639976938118397971148583)
    ·
      refine ⟨2459965407177596956722875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1639976938118397971148583 2459965407177596956722875)
      ·
        refine ⟨3689948110766395435084313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2459965407177596956722875 3689948110766395435084313)
        ·
          refine ⟨2767461083074796576313235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3689948110766395435084313 2767461083074796576313235)
          ·
            refine ⟨4151191624612194864469853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2767461083074796576313235 4151191624612194864469853)
            ·
              refine ⟨1556696859229573074176195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4151191624612194864469853 1556696859229573074176195)
              ·
                refine ⟨2335045288844359611264293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1556696859229573074176195 2335045288844359611264293)
                ·
                  refine ⟨437820991658317427112055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2335045288844359611264293 437820991658317427112055)
                  ·
                    rfl

theorem cell21_1918470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_1918470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1918470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1918470 prefixEnd_1918470 := by exact prefixLift 1918470
  have htrace : WordTrace (prefixWord ++ tailWord_1918470) baseStart_1918470 baseEnd_1918470 := by
    simpa [prefixWord, tailWord_1918470, baseEnd_1918470] using wordTrace_append hprefix tailTrace_1918470
  have hstable : (prefixWord ++ tailWord_1918470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918470).length < 2 ^ (prefixWord ++ tailWord_1918470).sum := by decide
  have hdescent : baseEnd_1918470 < baseStart_1918470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918551 : List Nat := [1, 1, 3, 2, 2, 3, 2, 7]
def baseStart_1918551 : Nat := 118140960795 + 1918551 * 2 ^ 59
def prefixEnd_1918551 : Nat := 4983230072969 + 3 ^ 40 * 1918551 * 2
def baseEnd_1918551 : Nat := 145946492320626428753963

theorem tailTrace_1918551 : CollatzResearch.WordTrace tailWord_1918551 prefixEnd_1918551 145946492320626428753963 := by
  unfold tailWord_1918551
  simp only [CollatzResearch.WordTrace]
  refine ⟨69975303672424864269371507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46650202448283242846247671 69975303672424864269371507)
  ·
    refine ⟨104962955508637296404057261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69975303672424864269371507 104962955508637296404057261)
    ·
      refine ⟨39361108315738986151521473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104962955508637296404057261 39361108315738986151521473)
      ·
        refine ⟨29520831236804239613641105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39361108315738986151521473 29520831236804239613641105)
        ·
          refine ⟨22140623427603179710230829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29520831236804239613641105 22140623427603179710230829)
          ·
            refine ⟨8302733785351192391336561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22140623427603179710230829 8302733785351192391336561)
            ·
              refine ⟨6227050339013394293502421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8302733785351192391336561 6227050339013394293502421)
              ·
                refine ⟨145946492320626428753963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6227050339013394293502421 145946492320626428753963)
                ·
                  rfl

theorem cell21_1918551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 7].length) (baseStart_1918551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1918551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1918551 prefixEnd_1918551 := by exact prefixLift 1918551
  have htrace : WordTrace (prefixWord ++ tailWord_1918551) baseStart_1918551 baseEnd_1918551 := by
    simpa [prefixWord, tailWord_1918551, baseEnd_1918551] using wordTrace_append hprefix tailTrace_1918551
  have hstable : (prefixWord ++ tailWord_1918551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918551).length < 2 ^ (prefixWord ++ tailWord_1918551).sum := by decide
  have hdescent : baseEnd_1918551 < baseStart_1918551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918574 : List Nat := [4, 1, 2, 2, 3, 2, 2, 2, 3]
def baseStart_1918574 : Nat := 118140960795 + 1918574 * 2 ^ 59
def prefixEnd_1918574 : Nat := 4983230072969 + 3 ^ 40 * 1918574 * 2
def baseEnd_1918574 : Nat := 437844725875236357378509

theorem tailTrace_1918574 : CollatzResearch.WordTrace tailWord_1918574 prefixEnd_1918574 437844725875236357378509 := by
  unfold tailWord_1918574
  simp only [CollatzResearch.WordTrace]
  refine ⟨8747017818917692399682347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46650761700894359464972517 8747017818917692399682347)
  ·
    refine ⟨13120526728376538599523521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8747017818917692399682347 13120526728376538599523521)
    ·
      refine ⟨9840395046282403949642641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13120526728376538599523521 9840395046282403949642641)
      ·
        refine ⟨7380296284711802962231981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9840395046282403949642641 7380296284711802962231981)
        ·
          refine ⟨2767611106766926110836993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7380296284711802962231981 2767611106766926110836993)
          ·
            refine ⟨2075708330075194583127745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2767611106766926110836993 2075708330075194583127745)
            ·
              refine ⟨1556781247556395937345809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2075708330075194583127745 1556781247556395937345809)
              ·
                refine ⟨1167585935667296953009357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1556781247556395937345809 1167585935667296953009357)
                ·
                  refine ⟨437844725875236357378509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1167585935667296953009357 437844725875236357378509)
                  ·
                    rfl

theorem cell21_1918574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_1918574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1918574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1918574 prefixEnd_1918574 := by exact prefixLift 1918574
  have htrace : WordTrace (prefixWord ++ tailWord_1918574) baseStart_1918574 baseEnd_1918574 := by
    simpa [prefixWord, tailWord_1918574, baseEnd_1918574] using wordTrace_append hprefix tailTrace_1918574
  have hstable : (prefixWord ++ tailWord_1918574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918574).length < 2 ^ (prefixWord ++ tailWord_1918574).sum := by decide
  have hdescent : baseEnd_1918574 < baseStart_1918574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918616 : List Nat := [2, 1, 2, 4, 1, 3, 2, 3, 3]
def baseStart_1918616 : Nat := 118140960795 + 1918616 * 2 ^ 59
def prefixEnd_1918616 : Nat := 4983230072969 + 3 ^ 40 * 1918616 * 2
def baseEnd_1918616 : Nat := 437854310847453617678423

theorem tailTrace_1918616 : CollatzResearch.WordTrace tailWord_1918616 prefixEnd_1918616 437854310847453617678423 := by
  unfold tailWord_1918616
  simp only [CollatzResearch.WordTrace]
  refine ⟨34988837208594690185243851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46651782944792920246991801 34988837208594690185243851)
  ·
    refine ⟨52483255812892035277865777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34988837208594690185243851 52483255812892035277865777)
    ·
      refine ⟨39362441859669026458399333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52483255812892035277865777 39362441859669026458399333)
      ·
        refine ⟨7380457848687942460949875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39362441859669026458399333 7380457848687942460949875)
        ·
          refine ⟨11070686773031913691424813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7380457848687942460949875 11070686773031913691424813)
          ·
            refine ⟨4151507539886967634284305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11070686773031913691424813 4151507539886967634284305)
            ·
              refine ⟨3113630654915225725713229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4151507539886967634284305 3113630654915225725713229)
              ·
                refine ⟨1167611495593209647142461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3113630654915225725713229 1167611495593209647142461)
                ·
                  refine ⟨437854310847453617678423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1167611495593209647142461 437854310847453617678423)
                  ·
                    rfl

theorem cell21_1918616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3, 3].length) (baseStart_1918616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1918616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1918616 prefixEnd_1918616 := by exact prefixLift 1918616
  have htrace : WordTrace (prefixWord ++ tailWord_1918616) baseStart_1918616 baseEnd_1918616 := by
    simpa [prefixWord, tailWord_1918616, baseEnd_1918616] using wordTrace_append hprefix tailTrace_1918616
  have hstable : (prefixWord ++ tailWord_1918616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918616).length < 2 ^ (prefixWord ++ tailWord_1918616).sum := by decide
  have hdescent : baseEnd_1918616 < baseStart_1918616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918678 : List Nat := [5, 2, 1, 3, 1, 2, 7]
def baseStart_1918678 : Nat := 118140960795 + 1918678 * 2 ^ 59
def prefixEnd_1918678 : Nat := 4983230072969 + 3 ^ 40 * 1918678 * 2
def baseEnd_1918678 : Nat := 48652051121350587516107

theorem tailTrace_1918678 : CollatzResearch.WordTrace tailWord_1918678 prefixEnd_1918678 48652051121350587516107 := by
  unfold tailWord_1918678
  simp only [CollatzResearch.WordTrace]
  refine ⟨4373745983935297809952793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46653290495309843306163125 4373745983935297809952793)
  ·
    refine ⟨3280309487951473357464595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4373745983935297809952793 3280309487951473357464595)
    ·
      refine ⟨4920464231927210036196893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3280309487951473357464595 4920464231927210036196893)
      ·
        refine ⟨1845174086972703763573835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4920464231927210036196893 1845174086972703763573835)
        ·
          refine ⟨2767761130459055645360753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1845174086972703763573835 2767761130459055645360753)
          ·
            refine ⟨2075820847844291734020565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2767761130459055645360753 2075820847844291734020565)
            ·
              refine ⟨48652051121350587516107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2075820847844291734020565 48652051121350587516107)
              ·
                rfl

theorem cell21_1918678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 7].length) (baseStart_1918678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1918678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1918678 prefixEnd_1918678 := by exact prefixLift 1918678
  have htrace : WordTrace (prefixWord ++ tailWord_1918678) baseStart_1918678 baseEnd_1918678 := by
    simpa [prefixWord, tailWord_1918678, baseEnd_1918678] using wordTrace_append hprefix tailTrace_1918678
  have hstable : (prefixWord ++ tailWord_1918678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918678).length < 2 ^ (prefixWord ++ tailWord_1918678).sum := by decide
  have hdescent : baseEnd_1918678 < baseStart_1918678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918692 : List Nat := [2, 3, 1, 1, 1, 3, 5, 2, 3]
def baseStart_1918692 : Nat := 118140960795 + 1918692 * 2 ^ 59
def prefixEnd_1918692 : Nat := 4983230072969 + 3 ^ 40 * 1918692 * 2
def baseEnd_1918692 : Nat := 437871655082894374411601

theorem tailTrace_1918692 : CollatzResearch.WordTrace tailWord_1918692 prefixEnd_1918692 437871655082894374411601 := by
  unfold tailWord_1918692
  simp only [CollatzResearch.WordTrace]
  refine ⟨34990223182457022675127165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46653630909942696900169553 34990223182457022675127165)
  ·
    refine ⟨13121333693421383503172687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34990223182457022675127165 13121333693421383503172687)
    ·
      refine ⟨19682000540132075254759031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13121333693421383503172687 19682000540132075254759031)
      ·
        refine ⟨29523000810198112882138547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19682000540132075254759031 29523000810198112882138547)
        ·
          refine ⟨44284501215297169323207821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29523000810198112882138547 44284501215297169323207821)
          ·
            refine ⟨16606687955736438496202933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44284501215297169323207821 16606687955736438496202933)
            ·
              refine ⟨1556876995850291109019025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16606687955736438496202933 1556876995850291109019025)
              ·
                refine ⟨1167657746887718331764269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1556876995850291109019025 1167657746887718331764269)
                ·
                  refine ⟨437871655082894374411601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1167657746887718331764269 437871655082894374411601)
                  ·
                    rfl

theorem cell21_1918692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_1918692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1918692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1918692 prefixEnd_1918692 := by exact prefixLift 1918692
  have htrace : WordTrace (prefixWord ++ tailWord_1918692) baseStart_1918692 baseEnd_1918692 := by
    simpa [prefixWord, tailWord_1918692, baseEnd_1918692] using wordTrace_append hprefix tailTrace_1918692
  have hstable : (prefixWord ++ tailWord_1918692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918692).length < 2 ^ (prefixWord ++ tailWord_1918692).sum := by decide
  have hdescent : baseEnd_1918692 < baseStart_1918692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918703 : List Nat := [1, 1, 2, 1, 5, 1, 4, 6]
def baseStart_1918703 : Nat := 118140960795 + 1918703 * 2 ^ 59
def prefixEnd_1918703 : Nat := 4983230072969 + 3 ^ 40 * 1918703 * 2
def baseEnd_1918703 : Nat := 145958055144253599909415

theorem tailTrace_1918703 : CollatzResearch.WordTrace tailWord_1918703 prefixEnd_1918703 145958055144253599909415 := by
  unfold tailWord_1918703
  simp only [CollatzResearch.WordTrace]
  refine ⟨69980847567874194228904763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46653898378582796152603175 69980847567874194228904763)
  ·
    refine ⟨104971271351811291343357145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69980847567874194228904763 104971271351811291343357145)
    ·
      refine ⟨78728453513858468507517859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104971271351811291343357145 78728453513858468507517859)
      ·
        refine ⟨118092680270787702761276789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78728453513858468507517859 118092680270787702761276789)
        ·
          refine ⟨11071188775386347133869699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118092680270787702761276789 11071188775386347133869699)
          ·
            refine ⟨16606783163079520700804549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11071188775386347133869699 16606783163079520700804549)
            ·
              refine ⟨3113771843077410131400853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16606783163079520700804549 3113771843077410131400853)
              ·
                refine ⟨145958055144253599909415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3113771843077410131400853 145958055144253599909415)
                ·
                  rfl

theorem cell21_1918703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 6].length) (baseStart_1918703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1918703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1918703 prefixEnd_1918703 := by exact prefixLift 1918703
  have htrace : WordTrace (prefixWord ++ tailWord_1918703) baseStart_1918703 baseEnd_1918703 := by
    simpa [prefixWord, tailWord_1918703, baseEnd_1918703] using wordTrace_append hprefix tailTrace_1918703
  have hstable : (prefixWord ++ tailWord_1918703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918703).length < 2 ^ (prefixWord ++ tailWord_1918703).sum := by decide
  have hdescent : baseEnd_1918703 < baseStart_1918703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918751 : List Nat := [1, 1, 2, 4, 2, 1, 3, 4, 3]
def baseStart_1918751 : Nat := 118140960795 + 1918751 * 2 ^ 59
def prefixEnd_1918751 : Nat := 4983230072969 + 3 ^ 40 * 1918751 * 2
def baseEnd_1918751 : Nat := 437885119686723382928147

theorem tailTrace_1918751 : CollatzResearch.WordTrace tailWord_1918751 prefixEnd_1918751 437885119686723382928147 := by
  unfold tailWord_1918751
  simp only [CollatzResearch.WordTrace]
  refine ⟨69982598271700298426652107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46655065514466865617768071 69982598271700298426652107)
  ·
    refine ⟨104973897407550447639978161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69982598271700298426652107 104973897407550447639978161)
    ·
      refine ⟨78730423055662835729983621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104973897407550447639978161 78730423055662835729983621)
      ·
        refine ⟨14761954322936781699371929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78730423055662835729983621 14761954322936781699371929)
        ·
          refine ⟨11071465742202586274528947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14761954322936781699371929 11071465742202586274528947)
          ·
            refine ⟨16607198613303879411793421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11071465742202586274528947 16607198613303879411793421)
            ·
              refine ⟨6227699479988954779422533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16607198613303879411793421 6227699479988954779422533)
              ·
                refine ⟨1167693652497929021141725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6227699479988954779422533 1167693652497929021141725)
                ·
                  refine ⟨437885119686723382928147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1167693652497929021141725 437885119686723382928147)
                  ·
                    rfl

theorem cell21_1918751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 4, 3].length) (baseStart_1918751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1918751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1918751 prefixEnd_1918751 := by exact prefixLift 1918751
  have htrace : WordTrace (prefixWord ++ tailWord_1918751) baseStart_1918751 baseEnd_1918751 := by
    simpa [prefixWord, tailWord_1918751, baseEnd_1918751] using wordTrace_append hprefix tailTrace_1918751
  have hstable : (prefixWord ++ tailWord_1918751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918751).length < 2 ^ (prefixWord ++ tailWord_1918751).sum := by decide
  have hdescent : baseEnd_1918751 < baseStart_1918751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918793 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 7]
def baseStart_1918793 : Nat := 118140960795 + 1918793 * 2 ^ 59
def prefixEnd_1918793 : Nat := 4983230072969 + 3 ^ 40 * 1918793 * 2
def baseEnd_1918793 : Nat := 437894704658940643228061

theorem tailTrace_1918793 : CollatzResearch.WordTrace tailWord_1918793 prefixEnd_1918793 437894704658940643228061 := by
  unfold tailWord_1918793
  simp only [CollatzResearch.WordTrace]
  refine ⟨69984130137548139599681033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46656086758365426399787355 69984130137548139599681033)
  ·
    refine ⟨52488097603161104699760775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69984130137548139599681033 52488097603161104699760775)
    ·
      refine ⟨78732146404741657049641163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52488097603161104699760775 78732146404741657049641163)
      ·
        refine ⟨118098219607112485574461745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78732146404741657049641163 118098219607112485574461745)
        ·
          refine ⟨88573664705334364180846309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118098219607112485574461745 88573664705334364180846309)
          ·
            refine ⟨16607562132250193283908683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88573664705334364180846309 16607562132250193283908683)
            ·
              refine ⟨24911343198375289925863025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16607562132250193283908683 24911343198375289925863025)
              ·
                refine ⟨18683507398781467444397269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24911343198375289925863025 18683507398781467444397269)
                ·
                  refine ⟨437894704658940643228061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18683507398781467444397269 437894704658940643228061)
                  ·
                    rfl

theorem cell21_1918793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 7].length) (baseStart_1918793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1918793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1918793 prefixEnd_1918793 := by exact prefixLift 1918793
  have htrace : WordTrace (prefixWord ++ tailWord_1918793) baseStart_1918793 baseEnd_1918793 := by
    simpa [prefixWord, tailWord_1918793, baseEnd_1918793] using wordTrace_append hprefix tailTrace_1918793
  have hstable : (prefixWord ++ tailWord_1918793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918793).length < 2 ^ (prefixWord ++ tailWord_1918793).sum := by decide
  have hdescent : baseEnd_1918793 < baseStart_1918793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918810 : List Nat := [3, 1, 1, 2, 1, 3, 4, 1, 5]
def baseStart_1918810 : Nat := 118140960795 + 1918810 * 2 ^ 59
def prefixEnd_1918810 : Nat := 4983230072969 + 3 ^ 40 * 1918810 * 2
def baseEnd_1918810 : Nat := 437898584290552391444693

theorem tailTrace_1918810 : CollatzResearch.WordTrace tailWord_1918810 prefixEnd_1918810 437898584290552391444693 := by
  unfold tailWord_1918810
  simp only [CollatzResearch.WordTrace]
  refine ⟨17496187544621637875762471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46656500118991034335366589 17496187544621637875762471)
  ·
    refine ⟨26244281316932456813643707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17496187544621637875762471 26244281316932456813643707)
    ·
      refine ⟨39366421975398685220465561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26244281316932456813643707 39366421975398685220465561)
      ·
        refine ⟨29524816481549013915349171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39366421975398685220465561 29524816481549013915349171)
        ·
          refine ⟨44287224722323520873023757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29524816481549013915349171 44287224722323520873023757)
          ·
            refine ⟨16607709270871320327383909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44287224722323520873023757 16607709270871320327383909)
            ·
              refine ⟨3113945488288372561384483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16607709270871320327383909 3113945488288372561384483)
              ·
                refine ⟨4670918232432558842076725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3113945488288372561384483 4670918232432558842076725)
                ·
                  refine ⟨437898584290552391444693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4670918232432558842076725 437898584290552391444693)
                  ·
                    rfl

theorem cell21_1918810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_1918810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1918810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1918810 prefixEnd_1918810 := by exact prefixLift 1918810
  have htrace : WordTrace (prefixWord ++ tailWord_1918810) baseStart_1918810 baseEnd_1918810 := by
    simpa [prefixWord, tailWord_1918810, baseEnd_1918810] using wordTrace_append hprefix tailTrace_1918810
  have hstable : (prefixWord ++ tailWord_1918810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918810).length < 2 ^ (prefixWord ++ tailWord_1918810).sum := by decide
  have hdescent : baseEnd_1918810 < baseStart_1918810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918920 : List Nat := [2, 1, 3, 1, 4, 1, 4, 2, 3]
def baseStart_1918920 : Nat := 118140960795 + 1918920 * 2 ^ 59
def prefixEnd_1918920 : Nat := 4983230072969 + 3 ^ 40 * 1918920 * 2
def baseEnd_1918920 : Nat := 437923687789216644611135

theorem tailTrace_1918920 : CollatzResearch.WordTrace tailWord_1918920 prefixEnd_1918920 437923687789216644611135 := by
  unfold tailWord_1918920
  simp only [CollatzResearch.WordTrace]
  refine ⟨34994381104044020144777107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46659174805392026859702809 34994381104044020144777107)
  ·
    refine ⟨52491571656066030217165661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34994381104044020144777107 52491571656066030217165661)
    ·
      refine ⟨19684339371024761331437123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52491571656066030217165661 19684339371024761331437123)
      ·
        refine ⟨29526509056537141997155685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19684339371024761331437123 29526509056537141997155685)
        ·
          refine ⟨5536220448100714124466691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29526509056537141997155685 5536220448100714124466691)
          ·
            refine ⟨8304330672151071186700037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5536220448100714124466691 8304330672151071186700037)
            ·
              refine ⟨1557062001028325847506257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8304330672151071186700037 1557062001028325847506257)
              ·
                refine ⟨1167796500771244385629693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1557062001028325847506257 1167796500771244385629693)
                ·
                  refine ⟨437923687789216644611135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1167796500771244385629693 437923687789216644611135)
                  ·
                    rfl

theorem cell21_1918920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2, 3].length) (baseStart_1918920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1918920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1918920 prefixEnd_1918920 := by exact prefixLift 1918920
  have htrace : WordTrace (prefixWord ++ tailWord_1918920) baseStart_1918920 baseEnd_1918920 := by
    simpa [prefixWord, tailWord_1918920, baseEnd_1918920] using wordTrace_append hprefix tailTrace_1918920
  have hstable : (prefixWord ++ tailWord_1918920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918920).length < 2 ^ (prefixWord ++ tailWord_1918920).sum := by decide
  have hdescent : baseEnd_1918920 < baseStart_1918920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918945 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 7]
def baseStart_1918945 : Nat := 118140960795 + 1918945 * 2 ^ 59
def prefixEnd_1918945 : Nat := 4983230072969 + 3 ^ 40 * 1918945 * 2
def baseEnd_1918945 : Nat := 437929393129822156694417

theorem tailTrace_1918945 : CollatzResearch.WordTrace tailWord_1918945 prefixEnd_1918945 437929393129822156694417 := by
  unfold tailWord_1918945
  simp only [CollatzResearch.WordTrace]
  refine ⟨69989674032997469559214289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46659782688664979706142859 69989674032997469559214289)
  ·
    refine ⟨52492255524748102169410717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69989674032997469559214289 52492255524748102169410717)
    ·
      refine ⟨19684595821780538313529019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52492255524748102169410717 19684595821780538313529019)
      ·
        refine ⟨29526893732670807470293529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19684595821780538313529019 29526893732670807470293529)
        ·
          refine ⟨22145170299503105602720147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29526893732670807470293529 22145170299503105602720147)
          ·
            refine ⟨33217755449254658404080221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22145170299503105602720147 33217755449254658404080221)
            ·
              refine ⟨12456658293470496901530083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33217755449254658404080221 12456658293470496901530083)
              ·
                refine ⟨18684987440205745352295125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12456658293470496901530083 18684987440205745352295125)
                ·
                  refine ⟨437929393129822156694417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18684987440205745352295125 437929393129822156694417)
                  ·
                    rfl

theorem cell21_1918945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 7].length) (baseStart_1918945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1918945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1918945 prefixEnd_1918945 := by exact prefixLift 1918945
  have htrace : WordTrace (prefixWord ++ tailWord_1918945) baseStart_1918945 baseEnd_1918945 := by
    simpa [prefixWord, tailWord_1918945, baseEnd_1918945] using wordTrace_append hprefix tailTrace_1918945
  have hstable : (prefixWord ++ tailWord_1918945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918945).length < 2 ^ (prefixWord ++ tailWord_1918945).sum := by decide
  have hdescent : baseEnd_1918945 < baseStart_1918945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918976 : List Nat := [2, 1, 1, 2, 1, 1, 1, 8, 4]
def baseStart_1918976 : Nat := 118140960795 + 1918976 * 2 ^ 59
def prefixEnd_1918976 : Nat := 4983230072969 + 3 ^ 40 * 1918976 * 2
def baseEnd_1918976 : Nat := 437936467752172991677687

theorem tailTrace_1918976 : CollatzResearch.WordTrace tailWord_1918976 prefixEnd_1918976 437936467752172991677687 := by
  unfold tailWord_1918976
  simp only [CollatzResearch.WordTrace]
  refine ⟨34995402347942580926796391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46660536463923441235728521 34995402347942580926796391)
  ·
    refine ⟨52493103521913871390194587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34995402347942580926796391 52493103521913871390194587)
    ·
      refine ⟨78739655282870807085291881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52493103521913871390194587 78739655282870807085291881)
      ·
        refine ⟨59054741462153105313968911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78739655282870807085291881 59054741462153105313968911)
        ·
          refine ⟨88582112193229657970953367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59054741462153105313968911 88582112193229657970953367)
          ·
            refine ⟨132873168289844486956430051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88582112193229657970953367 132873168289844486956430051)
            ·
              refine ⟨199309752434766730434645077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132873168289844486956430051 199309752434766730434645077)
              ·
                refine ⟨2335661161344922622280997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 199309752434766730434645077 2335661161344922622280997)
                ·
                  refine ⟨437936467752172991677687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2335661161344922622280997 437936467752172991677687)
                  ·
                    rfl

theorem cell21_1918976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 4].length) (baseStart_1918976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1918976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1918976 prefixEnd_1918976 := by exact prefixLift 1918976
  have htrace : WordTrace (prefixWord ++ tailWord_1918976) baseStart_1918976 baseEnd_1918976 := by
    simpa [prefixWord, tailWord_1918976, baseEnd_1918976] using wordTrace_append hprefix tailTrace_1918976
  have hstable : (prefixWord ++ tailWord_1918976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918976).length < 2 ^ (prefixWord ++ tailWord_1918976).sum := by decide
  have hdescent : baseEnd_1918976 < baseStart_1918976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919066 : List Nat := [3, 1, 1, 2, 1, 1, 3, 9]
def baseStart_1919066 : Nat := 118140960795 + 1919066 * 2 ^ 59
def prefixEnd_1919066 : Nat := 4983230072969 + 3 ^ 40 * 1919066 * 2
def baseEnd_1919066 : Nat := 145985668992784278392501

theorem tailTrace_1919066 : CollatzResearch.WordTrace tailWord_1919066 prefixEnd_1919066 145985668992784278392501 := by
  unfold tailWord_1919066
  simp only [CollatzResearch.WordTrace]
  refine ⟨17498521816389776806092263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46662724843706071482912701 17498521816389776806092263)
  ·
    refine ⟨26247782724584665209138395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17498521816389776806092263 26247782724584665209138395)
    ·
      refine ⟨39371674086876997813707593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26247782724584665209138395 39371674086876997813707593)
      ·
        refine ⟨29528755565157748360280695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39371674086876997813707593 29528755565157748360280695)
        ·
          refine ⟨44293133347736622540421043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29528755565157748360280695 44293133347736622540421043)
          ·
            refine ⟨66439700021604933810631565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44293133347736622540421043 66439700021604933810631565)
            ·
              refine ⟨24914887508101850178986837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66439700021604933810631565 24914887508101850178986837)
              ·
                refine ⟨145985668992784278392501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24914887508101850178986837 145985668992784278392501)
                ·
                  rfl

theorem cell21_1919066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 9].length) (baseStart_1919066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1919066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1919066 prefixEnd_1919066 := by exact prefixLift 1919066
  have htrace : WordTrace (prefixWord ++ tailWord_1919066) baseStart_1919066 baseEnd_1919066 := by
    simpa [prefixWord, tailWord_1919066, baseEnd_1919066] using wordTrace_append hprefix tailTrace_1919066
  have hstable : (prefixWord ++ tailWord_1919066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919066).length < 2 ^ (prefixWord ++ tailWord_1919066).sum := by decide
  have hdescent : baseEnd_1919066 < baseStart_1919066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919114 : List Nat := [3, 1, 2, 3, 1, 3, 1, 2, 5]
def baseStart_1919114 : Nat := 118140960795 + 1919114 * 2 ^ 59
def prefixEnd_1919114 : Nat := 4983230072969 + 3 ^ 40 * 1919114 * 2
def baseEnd_1919114 : Nat := 437967961232315418377405

theorem tailTrace_1919114 : CollatzResearch.WordTrace tailWord_1919114 prefixEnd_1919114 437967961232315418377405 := by
  unfold tailWord_1919114
  simp only [CollatzResearch.WordTrace]
  refine ⟨17498959492346302855529099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46663891979590140948077597 17498959492346302855529099)
  ·
    refine ⟨26248439238519454283293649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17498959492346302855529099 26248439238519454283293649)
    ·
      refine ⟨19686329428889590712470237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26248439238519454283293649 19686329428889590712470237)
      ·
        refine ⟨7382373535833596517176339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19686329428889590712470237 7382373535833596517176339)
        ·
          refine ⟨11073560303750394775764509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7382373535833596517176339 11073560303750394775764509)
          ·
            refine ⟨4152585113906398040911691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11073560303750394775764509 4152585113906398040911691)
            ·
              refine ⟨6228877670859597061367537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4152585113906398040911691 6228877670859597061367537)
              ·
                refine ⟨4671658253144697796025653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6228877670859597061367537 4671658253144697796025653)
                ·
                  refine ⟨437967961232315418377405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4671658253144697796025653 437967961232315418377405)
                  ·
                    rfl

theorem cell21_1919114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_1919114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1919114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1919114 prefixEnd_1919114 := by exact prefixLift 1919114
  have htrace : WordTrace (prefixWord ++ tailWord_1919114) baseStart_1919114 baseEnd_1919114 := by
    simpa [prefixWord, tailWord_1919114, baseEnd_1919114] using wordTrace_append hprefix tailTrace_1919114
  have hstable : (prefixWord ++ tailWord_1919114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919114).length < 2 ^ (prefixWord ++ tailWord_1919114).sum := by decide
  have hdescent : baseEnd_1919114 < baseStart_1919114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919173 : List Nat := [1, 3, 1, 1, 1, 1, 6, 2, 5]
def baseStart_1919173 : Nat := 118140960795 + 1919173 * 2 ^ 59
def prefixEnd_1919173 : Nat := 4983230072969 + 3 ^ 40 * 1919173 * 2
def baseEnd_1919173 : Nat := 437981425836144426893951

theorem tailTrace_1919173 : CollatzResearch.WordTrace tailWord_1919173 prefixEnd_1919173 437981425836144426893951 := by
  unfold tailWord_1919173
  simp only [CollatzResearch.WordTrace]
  refine ⟨69997989876171464498514173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46665326584114309665676115 69997989876171464498514173)
  ·
    refine ⟨26249246203564299186942815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69997989876171464498514173 26249246203564299186942815)
    ·
      refine ⟨39373869305346448780414223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26249246203564299186942815 39373869305346448780414223)
      ·
        refine ⟨59060803958019673170621335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39373869305346448780414223 59060803958019673170621335)
        ·
          refine ⟨88591205937029509755932003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59060803958019673170621335 88591205937029509755932003)
          ·
            refine ⟨132886808905544264633898005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88591205937029509755932003 132886808905544264633898005)
            ·
              refine ⟨6229069167447387404713969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 132886808905544264633898005 6229069167447387404713969)
              ·
                refine ⟨4671801875585540553535477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6229069167447387404713969 4671801875585540553535477)
                ·
                  refine ⟨437981425836144426893951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4671801875585540553535477 437981425836144426893951)
                  ·
                    rfl

theorem cell21_1919173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_1919173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1919173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1919173 prefixEnd_1919173 := by exact prefixLift 1919173
  have htrace : WordTrace (prefixWord ++ tailWord_1919173) baseStart_1919173 baseEnd_1919173 := by
    simpa [prefixWord, tailWord_1919173, baseEnd_1919173] using wordTrace_append hprefix tailTrace_1919173
  have hstable : (prefixWord ++ tailWord_1919173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919173).length < 2 ^ (prefixWord ++ tailWord_1919173).sum := by decide
  have hdescent : baseEnd_1919173 < baseStart_1919173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919204 : List Nat := [2, 3, 1, 1, 1, 2, 1, 6, 4]
def baseStart_1919204 : Nat := 118140960795 + 1919204 * 2 ^ 59
def prefixEnd_1919204 : Nat := 4983230072969 + 3 ^ 40 * 1919204 * 2
def baseEnd_1919204 : Nat := 437988500458495261877221

theorem tailTrace_1919204 : CollatzResearch.WordTrace tailWord_1919204 prefixEnd_1919204 437988500458495261877221 := by
  unfold tailWord_1919204
  simp only [CollatzResearch.WordTrace]
  refine ⟨34999560269529578396446333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46666080359372771195261777 34999560269529578396446333)
  ·
    refine ⟨13124835101073591898667375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34999560269529578396446333 13124835101073591898667375)
    ·
      refine ⟨19687252651610387848001063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13124835101073591898667375 19687252651610387848001063)
      ·
        refine ⟨29530878977415581772001595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19687252651610387848001063 29530878977415581772001595)
        ·
          refine ⟨44296318466123372658002393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29530878977415581772001595 44296318466123372658002393)
          ·
            refine ⟨33222238849592529493501795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44296318466123372658002393 33222238849592529493501795)
            ·
              refine ⟨49833358274388794240252693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33222238849592529493501795 49833358274388794240252693)
              ·
                refine ⟨2335938669111974730011845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49833358274388794240252693 2335938669111974730011845)
                ·
                  refine ⟨437988500458495261877221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2335938669111974730011845 437988500458495261877221)
                  ·
                    rfl

theorem cell21_1919204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_1919204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1919204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1919204 prefixEnd_1919204 := by exact prefixLift 1919204
  have htrace : WordTrace (prefixWord ++ tailWord_1919204) baseStart_1919204 baseEnd_1919204 := by
    simpa [prefixWord, tailWord_1919204, baseEnd_1919204] using wordTrace_append hprefix tailTrace_1919204
  have hstable : (prefixWord ++ tailWord_1919204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919204).length < 2 ^ (prefixWord ++ tailWord_1919204).sum := by decide
  have hdescent : baseEnd_1919204 < baseStart_1919204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919207 : List Nat := [1, 1, 5, 3, 1, 3, 1, 1, 5]
def baseStart_1919207 : Nat := 118140960795 + 1919207 * 2 ^ 59
def prefixEnd_1919207 : Nat := 4983230072969 + 3 ^ 40 * 1919207 * 2
def baseEnd_1919207 : Nat := 437989185099367923327215

theorem tailTrace_1919207 : CollatzResearch.WordTrace tailWord_1919207 prefixEnd_1919207 437989185099367923327215 := by
  unfold tailWord_1919207
  simp only [CollatzResearch.WordTrace]
  refine ⟨69999229958048288305251875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46666153305365525536834583 69999229958048288305251875)
  ·
    refine ⟨104998844937072432457877813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69999229958048288305251875 104998844937072432457877813)
    ·
      refine ⟨9843641712850540542926045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104998844937072432457877813 9843641712850540542926045)
      ·
        refine ⟨3691365642318952703597267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9843641712850540542926045 3691365642318952703597267)
        ·
          refine ⟨5537048463478429055395901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3691365642318952703597267 5537048463478429055395901)
          ·
            refine ⟨2076393173804410895773463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5537048463478429055395901 2076393173804410895773463)
            ·
              refine ⟨3114589760706616343660195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2076393173804410895773463 3114589760706616343660195)
              ·
                refine ⟨4671884641059924515490293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3114589760706616343660195 4671884641059924515490293)
                ·
                  refine ⟨437989185099367923327215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4671884641059924515490293 437989185099367923327215)
                  ·
                    rfl

theorem cell21_1919207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 5].length) (baseStart_1919207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1919207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1919207 prefixEnd_1919207 := by exact prefixLift 1919207
  have htrace : WordTrace (prefixWord ++ tailWord_1919207) baseStart_1919207 baseEnd_1919207 := by
    simpa [prefixWord, tailWord_1919207, baseEnd_1919207] using wordTrace_append hprefix tailTrace_1919207
  have hstable : (prefixWord ++ tailWord_1919207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919207).length < 2 ^ (prefixWord ++ tailWord_1919207).sum := by decide
  have hdescent : baseEnd_1919207 < baseStart_1919207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919382 : List Nat := [5, 3, 1, 2, 2, 1, 2, 1, 4]
def baseStart_1919382 : Nat := 118140960795 + 1919382 * 2 ^ 59
def prefixEnd_1919382 : Nat := 4983230072969 + 3 ^ 40 * 1919382 * 2
def baseEnd_1919382 : Nat := 438029122483606507910191

theorem tailTrace_1919382 : CollatzResearch.WordTrace tailWord_1919382 prefixEnd_1919382 438029122483606507910191 := by
  unfold tailWord_1919382
  simp only [CollatzResearch.WordTrace]
  refine ⟨4375350795775893324554525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46670408488276195461914933 4375350795775893324554525)
  ·
    refine ⟨1640756548415959996707947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4375350795775893324554525 1640756548415959996707947)
    ·
      refine ⟨2461134822623939995061921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1640756548415959996707947 2461134822623939995061921)
      ·
        refine ⟨1845851116967954996296441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2461134822623939995061921 1845851116967954996296441)
        ·
          refine ⟨1384388337725966247222331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1845851116967954996296441 1384388337725966247222331)
          ·
            refine ⟨2076582506588949370833497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1384388337725966247222331 2076582506588949370833497)
            ·
              refine ⟨1557436879941712028125123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2076582506588949370833497 1557436879941712028125123)
              ·
                refine ⟨2336155319912568042187685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1557436879941712028125123 2336155319912568042187685)
                ·
                  refine ⟨438029122483606507910191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2336155319912568042187685 438029122483606507910191)
                  ·
                    rfl

theorem cell21_1919382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_1919382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1919382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1919382 prefixEnd_1919382 := by exact prefixLift 1919382
  have htrace : WordTrace (prefixWord ++ tailWord_1919382) baseStart_1919382 baseEnd_1919382 := by
    simpa [prefixWord, tailWord_1919382, baseEnd_1919382] using wordTrace_append hprefix tailTrace_1919382
  have hstable : (prefixWord ++ tailWord_1919382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919382).length < 2 ^ (prefixWord ++ tailWord_1919382).sum := by decide
  have hdescent : baseEnd_1919382 < baseStart_1919382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919390 : List Nat := [4, 3, 1, 2, 1, 2, 1, 3, 4]
def baseStart_1919390 : Nat := 118140960795 + 1919390 * 2 ^ 59
def prefixEnd_1919390 : Nat := 4983230072969 + 3 ^ 40 * 1919390 * 2
def baseEnd_1919390 : Nat := 438030948192600271776841

theorem tailTrace_1919390 : CollatzResearch.WordTrace tailWord_1919390 prefixEnd_1919390 438030948192600271776841 := by
  unfold tailWord_1919390
  simp only [CollatzResearch.WordTrace]
  refine ⟨8750738064548163819895453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46670603010923540372775749 8750738064548163819895453)
  ·
    refine ⟨3281526774205561432460795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8750738064548163819895453 3281526774205561432460795)
    ·
      refine ⟨4922290161308342148691193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3281526774205561432460795 4922290161308342148691193)
      ·
        refine ⟨3691717620981256611518395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4922290161308342148691193 3691717620981256611518395)
        ·
          refine ⟨5537576431471884917277593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3691717620981256611518395 5537576431471884917277593)
          ·
            refine ⟨4153182323603913687958195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5537576431471884917277593 4153182323603913687958195)
            ·
              refine ⟨6229773485405870531937293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4153182323603913687958195 6229773485405870531937293)
              ·
                refine ⟨2336165057027201449476485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6229773485405870531937293 2336165057027201449476485)
                ·
                  refine ⟨438030948192600271776841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2336165057027201449476485 438030948192600271776841)
                  ·
                    rfl

theorem cell21_1919390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_1919390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1919390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1919390 prefixEnd_1919390 := by exact prefixLift 1919390
  have htrace : WordTrace (prefixWord ++ tailWord_1919390) baseStart_1919390 baseEnd_1919390 := by
    simpa [prefixWord, tailWord_1919390, baseEnd_1919390] using wordTrace_append hprefix tailTrace_1919390
  have hstable : (prefixWord ++ tailWord_1919390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919390).length < 2 ^ (prefixWord ++ tailWord_1919390).sum := by decide
  have hdescent : baseEnd_1919390 < baseStart_1919390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919432 : List Nat := [2, 1, 3, 1, 3, 2, 1, 4, 4]
def baseStart_1919432 : Nat := 118140960795 + 1919432 * 2 ^ 59
def prefixEnd_1919432 : Nat := 4983230072969 + 3 ^ 40 * 1919432 * 2
def baseEnd_1919432 : Nat := 438040533164817532076755

theorem tailTrace_1919432 : CollatzResearch.WordTrace tailWord_1919432 prefixEnd_1919432 438040533164817532076755 := by
  unfold tailWord_1919432
  simp only [CollatzResearch.WordTrace]
  refine ⟨35003718191116575866096275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46671624254822101154795033 35003718191116575866096275)
  ·
    refine ⟨52505577286674863799144413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35003718191116575866096275 52505577286674863799144413)
    ·
      refine ⟨19689591482503073924679155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52505577286674863799144413 19689591482503073924679155)
      ·
        refine ⟨29534387223754610887018733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19689591482503073924679155 29534387223754610887018733)
        ·
          refine ⟨11075395208907979082632025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29534387223754610887018733 11075395208907979082632025)
          ·
            refine ⟨8306546406680984311974019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11075395208907979082632025 8306546406680984311974019)
            ·
              refine ⟨12459819610021476467961029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8306546406680984311974019 12459819610021476467961029)
              ·
                refine ⟨2336216176879026837742693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12459819610021476467961029 2336216176879026837742693)
                ·
                  refine ⟨438040533164817532076755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2336216176879026837742693 438040533164817532076755)
                  ·
                    rfl

theorem cell21_1919432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 4].length) (baseStart_1919432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1919432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1919432 prefixEnd_1919432 := by exact prefixLift 1919432
  have htrace : WordTrace (prefixWord ++ tailWord_1919432) baseStart_1919432 baseEnd_1919432 := by
    simpa [prefixWord, tailWord_1919432, baseEnd_1919432] using wordTrace_append hprefix tailTrace_1919432
  have hstable : (prefixWord ++ tailWord_1919432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919432).length < 2 ^ (prefixWord ++ tailWord_1919432).sum := by decide
  have hdescent : baseEnd_1919432 < baseStart_1919432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919463 : List Nat := [1, 1, 5, 2, 1, 1, 5, 5]
def baseStart_1919463 : Nat := 118140960795 + 1919463 * 2 ^ 59
def prefixEnd_1919463 : Nat := 4983230072969 + 3 ^ 40 * 1919463 * 2
def baseEnd_1919463 : Nat := 146015869262389455686675

theorem tailTrace_1919463 : CollatzResearch.WordTrace tailWord_1919463 prefixEnd_1919463 146015869262389455686675 := by
  unfold tailWord_1919463
  simp only [CollatzResearch.WordTrace]
  refine ⟨70008567045120844026571043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46672378030080562684380695 70008567045120844026571043)
  ·
    refine ⟨105012850567681266039856565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70008567045120844026571043 105012850567681266039856565)
    ·
      refine ⟨9844954740720118691236553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105012850567681266039856565 9844954740720118691236553)
      ·
        refine ⟨7383716055540089018427415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9844954740720118691236553 7383716055540089018427415)
        ·
          refine ⟨11075574083310133527641123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7383716055540089018427415 11075574083310133527641123)
          ·
            refine ⟨16613361124965200291461685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11075574083310133527641123 16613361124965200291461685)
            ·
              refine ⟨1557502605465487527324533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16613361124965200291461685 1557502605465487527324533)
              ·
                refine ⟨146015869262389455686675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1557502605465487527324533 146015869262389455686675)
                ·
                  rfl

theorem cell21_1919463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 5].length) (baseStart_1919463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1919463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1919463 prefixEnd_1919463 := by exact prefixLift 1919463
  have htrace : WordTrace (prefixWord ++ tailWord_1919463) baseStart_1919463 baseEnd_1919463 := by
    simpa [prefixWord, tailWord_1919463, baseEnd_1919463] using wordTrace_append hprefix tailTrace_1919463
  have hstable : (prefixWord ++ tailWord_1919463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919463).length < 2 ^ (prefixWord ++ tailWord_1919463).sum := by decide
  have hdescent : baseEnd_1919463 < baseStart_1919463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919491 : List Nat := [1, 1, 1, 3, 2, 1, 5, 1, 6]
def baseStart_1919491 : Nat := 118140960795 + 1919491 * 2 ^ 59
def prefixEnd_1919491 : Nat := 4983230072969 + 3 ^ 40 * 1919491 * 2
def baseEnd_1919491 : Nat := 438053997768646540593301

theorem tailTrace_1919491 : CollatzResearch.WordTrace tailWord_1919491 prefixEnd_1919491 438053997768646540593301 := by
  unfold tailWord_1919491
  simp only [CollatzResearch.WordTrace]
  refine ⟨70009588289019404808590327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46673058859346269872393551 70009588289019404808590327)
  ·
    refine ⟨105014382433529107212885491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70009588289019404808590327 105014382433529107212885491)
    ·
      refine ⟨157521573650293660819328237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105014382433529107212885491 157521573650293660819328237)
      ·
        refine ⟨59070590118860122807248089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157521573650293660819328237 59070590118860122807248089)
        ·
          refine ⟨44302942589145092105436067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59070590118860122807248089 44302942589145092105436067)
          ·
            refine ⟨66454413883717638158154101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44302942589145092105436067 66454413883717638158154101)
            ·
              refine ⟨6230101301598528577326947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66454413883717638158154101 6230101301598528577326947)
              ·
                refine ⟨9345151952397792865990421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6230101301598528577326947 9345151952397792865990421)
                ·
                  refine ⟨438053997768646540593301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9345151952397792865990421 438053997768646540593301)
                  ·
                    rfl

theorem cell21_1919491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 6].length) (baseStart_1919491 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1919491 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1919491 prefixEnd_1919491 := by exact prefixLift 1919491
  have htrace : WordTrace (prefixWord ++ tailWord_1919491) baseStart_1919491 baseEnd_1919491 := by
    simpa [prefixWord, tailWord_1919491, baseEnd_1919491] using wordTrace_append hprefix tailTrace_1919491
  have hstable : (prefixWord ++ tailWord_1919491).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919491).length < 2 ^ (prefixWord ++ tailWord_1919491).sum := by decide
  have hdescent : baseEnd_1919491 < baseStart_1919491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919528 : List Nat := [2, 1, 5, 2, 1, 3, 1, 3, 3]
def baseStart_1919528 : Nat := 118140960795 + 1919528 * 2 ^ 59
def prefixEnd_1919528 : Nat := 4983230072969 + 3 ^ 40 * 1919528 * 2
def baseEnd_1919528 : Nat := 438062441672742698476559

theorem tailTrace_1919528 : CollatzResearch.WordTrace tailWord_1919528 prefixEnd_1919528 438062441672742698476559 := by
  unfold tailWord_1919528
  simp only [CollatzResearch.WordTrace]
  refine ⟨35005468894942680063843619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46673958526590240085124825 35005468894942680063843619)
  ·
    refine ⟨52508203342414020095765429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35005468894942680063843619 52508203342414020095765429)
    ·
      refine ⟨4922644063351314383978009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52508203342414020095765429 4922644063351314383978009)
      ·
        refine ⟨3691983047513485787983507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4922644063351314383978009 3691983047513485787983507)
        ·
          refine ⟨5537974571270228681975261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3691983047513485787983507 5537974571270228681975261)
          ·
            refine ⟨2076740464226335755740723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5537974571270228681975261 2076740464226335755740723)
            ·
              refine ⟨3115110696339503633611085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2076740464226335755740723 3115110696339503633611085)
              ·
                refine ⟨1168166511127313862604157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3115110696339503633611085 1168166511127313862604157)
                ·
                  refine ⟨438062441672742698476559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1168166511127313862604157 438062441672742698476559)
                  ·
                    rfl

theorem cell21_1919528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3, 3].length) (baseStart_1919528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1919528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1919528 prefixEnd_1919528 := by exact prefixLift 1919528
  have htrace : WordTrace (prefixWord ++ tailWord_1919528) baseStart_1919528 baseEnd_1919528 := by
    simpa [prefixWord, tailWord_1919528, baseEnd_1919528] using wordTrace_append hprefix tailTrace_1919528
  have hstable : (prefixWord ++ tailWord_1919528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919528).length < 2 ^ (prefixWord ++ tailWord_1919528).sum := by decide
  have hdescent : baseEnd_1919528 < baseStart_1919528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919536 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 7]
def baseStart_1919536 : Nat := 118140960795 + 1919536 * 2 ^ 59
def prefixEnd_1919536 : Nat := 4983230072969 + 3 ^ 40 * 1919536 * 2
def baseEnd_1919536 : Nat := 438064267381736462343209

theorem tailTrace_1919536 : CollatzResearch.WordTrace tailWord_1919536 prefixEnd_1919536 438064267381736462343209 := by
  unfold tailWord_1919536
  simp only [CollatzResearch.WordTrace]
  refine ⟨35005614786928188746989231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46674153049237584995985641 35005614786928188746989231)
  ·
    refine ⟨52508422180392283120483847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35005614786928188746989231 52508422180392283120483847)
    ·
      refine ⟨78762633270588424680725771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52508422180392283120483847 78762633270588424680725771)
      ·
        refine ⟨118143949905882637021088657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78762633270588424680725771 118143949905882637021088657)
        ·
          refine ⟨88607962429411977765816493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118143949905882637021088657 88607962429411977765816493)
          ·
            refine ⟨33227985911029491662181185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88607962429411977765816493 33227985911029491662181185)
            ·
              refine ⟨24920989433272118746635889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33227985911029491662181185 24920989433272118746635889)
              ·
                refine ⟨18690742074954089059976917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24920989433272118746635889 18690742074954089059976917)
                ·
                  refine ⟨438064267381736462343209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18690742074954089059976917 438064267381736462343209)
                  ·
                    rfl

theorem cell21_1919536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 7].length) (baseStart_1919536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1919536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1919536 prefixEnd_1919536 := by exact prefixLift 1919536
  have htrace : WordTrace (prefixWord ++ tailWord_1919536) baseStart_1919536 baseEnd_1919536 := by
    simpa [prefixWord, tailWord_1919536, baseEnd_1919536] using wordTrace_append hprefix tailTrace_1919536
  have hstable : (prefixWord ++ tailWord_1919536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919536).length < 2 ^ (prefixWord ++ tailWord_1919536).sum := by decide
  have hdescent : baseEnd_1919536 < baseStart_1919536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919598 : List Nat := [4, 1, 2, 2, 2, 10]
def baseStart_1919598 : Nat := 118140960795 + 1919598 * 2 ^ 59
def prefixEnd_1919598 : Nat := 4983230072969 + 3 ^ 40 * 1919598 * 2
def baseEnd_1919598 : Nat := 16225126541719930826287

theorem tailTrace_1919598 : CollatzResearch.WordTrace tailWord_1919598 prefixEnd_1919598 16225126541719930826287 := by
  unfold tailWord_1919598
  simp only [CollatzResearch.WordTrace]
  refine ⟨8751686362453970260341931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46675660599754508055156965 8751686362453970260341931)
  ·
    refine ⟨13127529543680955390512897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8751686362453970260341931 13127529543680955390512897)
    ·
      refine ⟨9845647157760716542884673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13127529543680955390512897 9845647157760716542884673)
      ·
        refine ⟨7384235368320537407163505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9845647157760716542884673 7384235368320537407163505)
        ·
          refine ⟨5538176526240403055372629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7384235368320537407163505 5538176526240403055372629)
          ·
            refine ⟨16225126541719930826287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5538176526240403055372629 16225126541719930826287)
            ·
              rfl

theorem cell21_1919598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 10].length) (baseStart_1919598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1919598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1919598 prefixEnd_1919598 := by exact prefixLift 1919598
  have htrace : WordTrace (prefixWord ++ tailWord_1919598) baseStart_1919598 baseEnd_1919598 := by
    simpa [prefixWord, tailWord_1919598, baseEnd_1919598] using wordTrace_append hprefix tailTrace_1919598
  have hstable : (prefixWord ++ tailWord_1919598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919598).length < 2 ^ (prefixWord ++ tailWord_1919598).sum := by decide
  have hdescent : baseEnd_1919598 < baseStart_1919598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919677 : List Nat := [1, 4, 1, 2, 1, 4, 3, 1, 4]
def baseStart_1919677 : Nat := 118140960795 + 1919677 * 2 ^ 59
def prefixEnd_1919677 : Nat := 4983230072969 + 3 ^ 40 * 1919677 * 2
def baseEnd_1919677 : Nat := 438096445502751550492921

theorem tailTrace_1919677 : CollatzResearch.WordTrace tailWord_1919677 prefixEnd_1919677 438096445502751550492921 := by
  unfold tailWord_1919677
  simp only [CollatzResearch.WordTrace]
  refine ⟨70016372266345558574861285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46677581510897039049907523 70016372266345558574861285)
  ·
    refine ⟨13128069799939792232786491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70016372266345558574861285 13128069799939792232786491)
    ·
      refine ⟨19692104699909688349179737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13128069799939792232786491 19692104699909688349179737)
      ·
        refine ⟨14769078524932266261884803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19692104699909688349179737 14769078524932266261884803)
        ·
          refine ⟨22153617787398399392827205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14769078524932266261884803 22153617787398399392827205)
          ·
            refine ⟨4153803335137199886155101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22153617787398399392827205 4153803335137199886155101)
            ·
              refine ⟨1557676250676449957308163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4153803335137199886155101 1557676250676449957308163)
              ·
                refine ⟨2336514376014674935962245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1557676250676449957308163 2336514376014674935962245)
                ·
                  refine ⟨438096445502751550492921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2336514376014674935962245 438096445502751550492921)
                  ·
                    rfl

theorem cell21_1919677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_1919677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1919677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1919677 prefixEnd_1919677 := by exact prefixLift 1919677
  have htrace : WordTrace (prefixWord ++ tailWord_1919677) baseStart_1919677 baseEnd_1919677 := by
    simpa [prefixWord, tailWord_1919677, baseEnd_1919677] using wordTrace_append hprefix tailTrace_1919677
  have hstable : (prefixWord ++ tailWord_1919677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919677).length < 2 ^ (prefixWord ++ tailWord_1919677).sum := by decide
  have hdescent : baseEnd_1919677 < baseStart_1919677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919773 : List Nat := [1, 4, 2, 4, 1, 2, 2, 2, 3]
def baseStart_1919773 : Nat := 118140960795 + 1919773 * 2 ^ 59
def prefixEnd_1919773 : Nat := 4983230072969 + 3 ^ 40 * 1919773 * 2
def baseEnd_1919773 : Nat := 438118354010676716892725

theorem tailTrace_1919773 : CollatzResearch.WordTrace tailWord_1919773 prefixEnd_1919773 438118354010676716892725 := by
  unfold tailWord_1919773
  simp only [CollatzResearch.WordTrace]
  refine ⟨70019873673997766970355973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46679915782665177980237315 70019873673997766970355973)
  ·
    refine ⟨13128726313874581306941745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70019873673997766970355973 13128726313874581306941745)
    ·
      refine ⟨9846544735405935980206309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13128726313874581306941745 9846544735405935980206309)
      ·
        refine ⟨1846227137888612996288683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9846544735405935980206309 1846227137888612996288683)
        ·
          refine ⟨2769340706832919494433025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1846227137888612996288683 2769340706832919494433025)
          ·
            refine ⟨2077005530124689620824769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2769340706832919494433025 2077005530124689620824769)
            ·
              refine ⟨1557754147593517215618577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2077005530124689620824769 1557754147593517215618577)
              ·
                refine ⟨1168315610695137911713933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1557754147593517215618577 1168315610695137911713933)
                ·
                  refine ⟨438118354010676716892725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1168315610695137911713933 438118354010676716892725)
                  ·
                    rfl

theorem cell21_1919773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_1919773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1919773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1919773 prefixEnd_1919773 := by exact prefixLift 1919773
  have htrace : WordTrace (prefixWord ++ tailWord_1919773) baseStart_1919773 baseEnd_1919773 := by
    simpa [prefixWord, tailWord_1919773, baseEnd_1919773] using wordTrace_append hprefix tailTrace_1919773
  have hstable : (prefixWord ++ tailWord_1919773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919773).length < 2 ^ (prefixWord ++ tailWord_1919773).sum := by decide
  have hdescent : baseEnd_1919773 < baseStart_1919773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919905 : List Nat := [1, 2, 3, 4, 1, 1, 4, 1, 4]
def baseStart_1919905 : Nat := 118140960795 + 1919905 * 2 ^ 59
def prefixEnd_1919905 : Nat := 4983230072969 + 3 ^ 40 * 1919905 * 2
def baseEnd_1919905 : Nat := 438148478209073820692455

theorem tailTrace_1919905 : CollatzResearch.WordTrace tailWord_1919905 prefixEnd_1919905 438148478209073820692455 := by
  unfold tailWord_1919905
  simp only [CollatzResearch.WordTrace]
  refine ⟨70024688109519553514161169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46683125406346369009440779 70024688109519553514161169)
  ·
    refine ⟨52518516082139665135620877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70024688109519553514161169 52518516082139665135620877)
    ·
      refine ⟨19694443530802374425857829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52518516082139665135620877 19694443530802374425857829)
      ·
        refine ⟨3692708162025445204848343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19694443530802374425857829 3692708162025445204848343)
        ·
          refine ⟨5539062243038167807272515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3692708162025445204848343 5539062243038167807272515)
          ·
            refine ⟨8308593364557251710908773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5539062243038167807272515 8308593364557251710908773)
            ·
              refine ⟨1557861255854484695795395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8308593364557251710908773 1557861255854484695795395)
              ·
                refine ⟨2336791883781727043693093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1557861255854484695795395 2336791883781727043693093)
                ·
                  refine ⟨438148478209073820692455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2336791883781727043693093 438148478209073820692455)
                  ·
                    rfl

theorem cell21_1919905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 4].length) (baseStart_1919905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1919905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1919905 prefixEnd_1919905 := by exact prefixLift 1919905
  have htrace : WordTrace (prefixWord ++ tailWord_1919905) baseStart_1919905 baseEnd_1919905 := by
    simpa [prefixWord, tailWord_1919905, baseEnd_1919905] using wordTrace_append hprefix tailTrace_1919905
  have hstable : (prefixWord ++ tailWord_1919905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919905).length < 2 ^ (prefixWord ++ tailWord_1919905).sum := by decide
  have hdescent : baseEnd_1919905 < baseStart_1919905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919942 : List Nat := [6, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_1919942 : Nat := 118140960795 + 1919942 * 2 ^ 59
def prefixEnd_1919942 : Nat := 4983230072969 + 3 ^ 40 * 1919942 * 2
def baseEnd_1919942 : Nat := 438156922113169978575713

theorem tailTrace_1919942 : CollatzResearch.WordTrace tailWord_1919942 prefixEnd_1919942 438156922113169978575713 := by
  unfold tailWord_1919942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2188313675324547151039315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46684025073590339222172053 2188313675324547151039315)
  ·
    refine ⟨3282470512986820726558973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2188313675324547151039315 3282470512986820726558973)
    ·
      refine ⟨1230926442370057772459615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3282470512986820726558973 1230926442370057772459615)
      ·
        refine ⟨1846389663555086658689423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1230926442370057772459615 1846389663555086658689423)
        ·
          refine ⟨2769584495332629988034135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1846389663555086658689423 2769584495332629988034135)
          ·
            refine ⟨4154376742998944982051203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2769584495332629988034135 4154376742998944982051203)
            ·
              refine ⟨6231565114498417473076805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4154376742998944982051203 6231565114498417473076805)
              ·
                refine ⟨1168418458968453276201901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6231565114498417473076805 1168418458968453276201901)
                ·
                  refine ⟨438156922113169978575713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1168418458968453276201901 438156922113169978575713)
                  ·
                    rfl

theorem cell21_1919942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_1919942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1919942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1919942 prefixEnd_1919942 := by exact prefixLift 1919942
  have htrace : WordTrace (prefixWord ++ tailWord_1919942) baseStart_1919942 baseEnd_1919942 := by
    simpa [prefixWord, tailWord_1919942, baseEnd_1919942] using wordTrace_append hprefix tailTrace_1919942
  have hstable : (prefixWord ++ tailWord_1919942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919942).length < 2 ^ (prefixWord ++ tailWord_1919942).sum := by decide
  have hdescent : baseEnd_1919942 < baseStart_1919942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919947 : List Nat := [1, 1, 1, 1, 3, 5, 1, 4, 4]
def baseStart_1919947 : Nat := 118140960795 + 1919947 * 2 ^ 59
def prefixEnd_1919947 : Nat := 4983230072969 + 3 ^ 40 * 1919947 * 2
def baseEnd_1919947 : Nat := 438158063181291080992369

theorem tailTrace_1919947 : CollatzResearch.WordTrace tailWord_1919947 prefixEnd_1919947 438158063181291080992369 := by
  unfold tailWord_1919947
  simp only [CollatzResearch.WordTrace]
  refine ⟨70026219975367394687190095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46684146650244929791460063 70026219975367394687190095)
  ·
    refine ⟨105039329963051092030785143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70026219975367394687190095 105039329963051092030785143)
    ·
      refine ⟨157558994944576638046177715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105039329963051092030785143 157558994944576638046177715)
      ·
        refine ⟨236338492416864957069266573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157558994944576638046177715 236338492416864957069266573)
        ·
          refine ⟨88626934656324358900974965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236338492416864957069266573 88626934656324358900974965)
          ·
            refine ⟨8308775124030408646966403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88626934656324358900974965 8308775124030408646966403)
            ·
              refine ⟨12463162686045612970449605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8308775124030408646966403 12463162686045612970449605)
              ·
                refine ⟨2336843003633552431959301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12463162686045612970449605 2336843003633552431959301)
                ·
                  refine ⟨438158063181291080992369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2336843003633552431959301 438158063181291080992369)
                  ·
                    rfl

theorem cell21_1919947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 4].length) (baseStart_1919947 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1919947 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1919947 prefixEnd_1919947 := by exact prefixLift 1919947
  have htrace : WordTrace (prefixWord ++ tailWord_1919947) baseStart_1919947 baseEnd_1919947 := by
    simpa [prefixWord, tailWord_1919947, baseEnd_1919947] using wordTrace_append hprefix tailTrace_1919947
  have hstable : (prefixWord ++ tailWord_1919947).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919947).length < 2 ^ (prefixWord ++ tailWord_1919947).sum := by decide
  have hdescent : baseEnd_1919947 < baseStart_1919947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919950 : List Nat := [4, 1, 1, 1, 2, 4, 1, 4, 3]
def baseStart_1919950 : Nat := 118140960795 + 1919950 * 2 ^ 59
def prefixEnd_1919950 : Nat := 4983230072969 + 3 ^ 40 * 1919950 * 2
def baseEnd_1919950 : Nat := 438158747822163742442363

theorem tailTrace_1919950 : CollatzResearch.WordTrace tailWord_1919950 prefixEnd_1919950 438158747822163742442363 := by
  unfold tailWord_1919950
  simp only [CollatzResearch.WordTrace]
  refine ⟨8753291174294565774943663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46684219596237684133032869 8753291174294565774943663)
  ·
    refine ⟨13129936761441848662415495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8753291174294565774943663 13129936761441848662415495)
    ·
      refine ⟨19694905142162772993623243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13129936761441848662415495 19694905142162772993623243)
      ·
        refine ⟨29542357713244159490434865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19694905142162772993623243 29542357713244159490434865)
        ·
          refine ⟨22156768284933119617826149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29542357713244159490434865 22156768284933119617826149)
          ·
            refine ⟨4154394053424959928342403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22156768284933119617826149 4154394053424959928342403)
            ·
              refine ⟨6231591080137439892513605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4154394053424959928342403 6231591080137439892513605)
              ·
                refine ⟨1168423327525769979846301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6231591080137439892513605 1168423327525769979846301)
                ·
                  refine ⟨438158747822163742442363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1168423327525769979846301 438158747822163742442363)
                  ·
                    rfl

theorem cell21_1919950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_1919950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1919950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1919950 prefixEnd_1919950 := by exact prefixLift 1919950
  have htrace : WordTrace (prefixWord ++ tailWord_1919950) baseStart_1919950 baseEnd_1919950 := by
    simpa [prefixWord, tailWord_1919950, baseEnd_1919950] using wordTrace_append hprefix tailTrace_1919950
  have hstable : (prefixWord ++ tailWord_1919950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919950).length < 2 ^ (prefixWord ++ tailWord_1919950).sum := by decide
  have hdescent : baseEnd_1919950 < baseStart_1919950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919998 : List Nat := [4, 2, 2, 2, 2, 2, 1, 2, 4]
def baseStart_1919998 : Nat := 118140960795 + 1919998 * 2 ^ 59
def prefixEnd_1919998 : Nat := 4983230072969 + 3 ^ 40 * 1919998 * 2
def baseEnd_1919998 : Nat := 438169702076126325642265

theorem tailTrace_1919998 : CollatzResearch.WordTrace tailWord_1919998 prefixEnd_1919998 438169702076126325642265 := by
  unfold tailWord_1919998
  simp only [CollatzResearch.WordTrace]
  refine ⟨8753510012272828799662081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46685386732121753598197765 8753510012272828799662081)
  ·
    refine ⟨6565132509204621599746561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8753510012272828799662081 6565132509204621599746561)
    ·
      refine ⟨4923849381903466199809921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6565132509204621599746561 4923849381903466199809921)
      ·
        refine ⟨3692887036427599649857441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4923849381903466199809921 3692887036427599649857441)
        ·
          refine ⟨2769665277320699737393081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3692887036427599649857441 2769665277320699737393081)
          ·
            refine ⟨2077248957990524803044811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2769665277320699737393081 2077248957990524803044811)
            ·
              refine ⟨3115873436985787204567217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2077248957990524803044811 3115873436985787204567217)
              ·
                refine ⟨2336905077739340403425413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3115873436985787204567217 2336905077739340403425413)
                ·
                  refine ⟨438169702076126325642265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2336905077739340403425413 438169702076126325642265)
                  ·
                    rfl

theorem cell21_1919998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_1919998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1919998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1919998 prefixEnd_1919998 := by exact prefixLift 1919998
  have htrace : WordTrace (prefixWord ++ tailWord_1919998) baseStart_1919998 baseEnd_1919998 := by
    simpa [prefixWord, tailWord_1919998, baseEnd_1919998] using wordTrace_append hprefix tailTrace_1919998
  have hstable : (prefixWord ++ tailWord_1919998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919998).length < 2 ^ (prefixWord ++ tailWord_1919998).sum := by decide
  have hdescent : baseEnd_1919998 < baseStart_1919998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920037 : List Nat := [1, 3, 1, 2, 2, 2, 3, 7]
def baseStart_1920037 : Nat := 118140960795 + 1920037 * 2 ^ 59
def prefixEnd_1920037 : Nat := 4983230072969 + 3 ^ 40 * 1920037 * 2
def baseEnd_1920037 : Nat := 146059534135823641497395

theorem tailTrace_1920037 : CollatzResearch.WordTrace tailWord_1920037 prefixEnd_1920037 146059534135823641497395 := by
  unfold tailWord_1920037
  simp only [CollatzResearch.WordTrace]
  refine ⟨70029502545041340057966365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46686335030027560038644243 70029502545041340057966365)
  ·
    refine ⟨26261063454390502521737387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70029502545041340057966365 26261063454390502521737387)
    ·
      refine ⟨39391595181585753782606081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26261063454390502521737387 39391595181585753782606081)
      ·
        refine ⟨29543696386189315336954561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39391595181585753782606081 29543696386189315336954561)
        ·
          refine ⟨22157772289641986502715921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29543696386189315336954561 22157772289641986502715921)
          ·
            refine ⟨16618329217231489877036941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22157772289641986502715921 16618329217231489877036941)
            ·
              refine ⟨6231873456461808703888853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16618329217231489877036941 6231873456461808703888853)
              ·
                refine ⟨146059534135823641497395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6231873456461808703888853 146059534135823641497395)
                ·
                  rfl

theorem cell21_1920037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 7].length) (baseStart_1920037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1920037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1920037 prefixEnd_1920037 := by exact prefixLift 1920037
  have htrace : WordTrace (prefixWord ++ tailWord_1920037) baseStart_1920037 baseEnd_1920037 := by
    simpa [prefixWord, tailWord_1920037, baseEnd_1920037] using wordTrace_append hprefix tailTrace_1920037
  have hstable : (prefixWord ++ tailWord_1920037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920037).length < 2 ^ (prefixWord ++ tailWord_1920037).sum := by decide
  have hdescent : baseEnd_1920037 < baseStart_1920037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920054 : List Nat := [5, 1, 2, 1, 1, 2, 9]
def baseStart_1920054 : Nat := 118140960795 + 1920054 * 2 ^ 59
def prefixEnd_1920054 : Nat := 4983230072969 + 3 ^ 40 * 1920054 * 2
def baseEnd_1920054 : Nat := 48686942448786963634313

theorem tailTrace_1920054 : CollatzResearch.WordTrace tailWord_1920054 prefixEnd_1920054 48686942448786963634313 := by
  unfold tailWord_1920054
  simp only [CollatzResearch.WordTrace]
  refine ⟨4376882661623734497583451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46686748390653167974223477 4376882661623734497583451)
  ·
    refine ⟨6565323992435601746375177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4376882661623734497583451 6565323992435601746375177)
    ·
      refine ⟨4923992994326701309781383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6565323992435601746375177 4923992994326701309781383)
      ·
        refine ⟨7385989491490051964672075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4923992994326701309781383 7385989491490051964672075)
        ·
          refine ⟨11078984237235077947008113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7385989491490051964672075 11078984237235077947008113)
          ·
            refine ⟨8309238177926308460256085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11078984237235077947008113 8309238177926308460256085)
            ·
              refine ⟨48686942448786963634313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8309238177926308460256085 48686942448786963634313)
              ·
                rfl

theorem cell21_1920054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 9].length) (baseStart_1920054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1920054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1920054 prefixEnd_1920054 := by exact prefixLift 1920054
  have htrace : WordTrace (prefixWord ++ tailWord_1920054) baseStart_1920054 baseEnd_1920054 := by
    simpa [prefixWord, tailWord_1920054, baseEnd_1920054] using wordTrace_append hprefix tailTrace_1920054
  have hstable : (prefixWord ++ tailWord_1920054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920054).length < 2 ^ (prefixWord ++ tailWord_1920054).sum := by decide
  have hdescent : baseEnd_1920054 < baseStart_1920054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920127 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 11]
def baseStart_1920127 : Nat := 118140960795 + 1920127 * 2 ^ 59
def prefixEnd_1920127 : Nat := 4983230072969 + 3 ^ 40 * 1920127 * 2
def baseEnd_1920127 : Nat := 438199141633650767992001

theorem tailTrace_1920127 : CollatzResearch.WordTrace tailWord_1920127 prefixEnd_1920127 438199141633650767992001 := by
  unfold tailWord_1920127
  simp only [CollatzResearch.WordTrace]
  refine ⟨70032785114715285428742635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46688523409810190285828423 70032785114715285428742635)
  ·
    refine ⟨105049177672072928143113953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70032785114715285428742635 105049177672072928143113953)
    ·
      refine ⟨78786883254054696107335465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105049177672072928143113953 78786883254054696107335465)
      ·
        refine ⟨59090162440541022080501599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78786883254054696107335465 59090162440541022080501599)
        ·
          refine ⟨88635243660811533120752399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59090162440541022080501599 88635243660811533120752399)
          ·
            refine ⟨132952865491217299681128599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88635243660811533120752399 132952865491217299681128599)
            ·
              refine ⟨199429298236825949521692899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132952865491217299681128599 199429298236825949521692899)
              ·
                refine ⟨299143947355238924282539349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199429298236825949521692899 299143947355238924282539349)
                ·
                  refine ⟨438199141633650767992001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 299143947355238924282539349 438199141633650767992001)
                  ·
                    rfl

theorem cell21_1920127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 11].length) (baseStart_1920127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1920127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1920127 prefixEnd_1920127 := by exact prefixLift 1920127
  have htrace : WordTrace (prefixWord ++ tailWord_1920127) baseStart_1920127 baseEnd_1920127 := by
    simpa [prefixWord, tailWord_1920127, baseEnd_1920127] using wordTrace_append hprefix tailTrace_1920127
  have hstable : (prefixWord ++ tailWord_1920127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920127).length < 2 ^ (prefixWord ++ tailWord_1920127).sum := by decide
  have hdescent : baseEnd_1920127 < baseStart_1920127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920175 : List Nat := [1, 1, 2, 1, 2, 3, 5, 2, 4]
def baseStart_1920175 : Nat := 118140960795 + 1920175 * 2 ^ 59
def prefixEnd_1920175 : Nat := 4983230072969 + 3 ^ 40 * 1920175 * 2
def baseEnd_1920175 : Nat := 438210095887613351191903

theorem tailTrace_1920175 : CollatzResearch.WordTrace tailWord_1920175 prefixEnd_1920175 438210095887613351191903 := by
  unfold tailWord_1920175
  simp only [CollatzResearch.WordTrace]
  refine ⟨70034535818541389626489979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46689690545694259750993319 70034535818541389626489979)
  ·
    refine ⟨105051803727812084439734969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70034535818541389626489979 105051803727812084439734969)
    ·
      refine ⟨78788852795859063329801227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105051803727812084439734969 78788852795859063329801227)
      ·
        refine ⟨118183279193788594994701841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78788852795859063329801227 118183279193788594994701841)
        ·
          refine ⟨88637459395341446246026381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118183279193788594994701841 88637459395341446246026381)
          ·
            refine ⟨33239047273253042342259893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88637459395341446246026381 33239047273253042342259893)
            ·
              refine ⟨3116160681867472719586865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33239047273253042342259893 3116160681867472719586865)
              ·
                refine ⟨2337120511400604539690149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3116160681867472719586865 2337120511400604539690149)
                ·
                  refine ⟨438210095887613351191903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2337120511400604539690149 438210095887613351191903)
                  ·
                    rfl

theorem cell21_1920175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 4].length) (baseStart_1920175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1920175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1920175 prefixEnd_1920175 := by exact prefixLift 1920175
  have htrace : WordTrace (prefixWord ++ tailWord_1920175) baseStart_1920175 baseEnd_1920175 := by
    simpa [prefixWord, tailWord_1920175, baseEnd_1920175] using wordTrace_append hprefix tailTrace_1920175
  have hstable : (prefixWord ++ tailWord_1920175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920175).length < 2 ^ (prefixWord ++ tailWord_1920175).sum := by decide
  have hdescent : baseEnd_1920175 < baseStart_1920175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920198 : List Nat := [6, 1, 2, 2, 1, 2, 2, 5]
def baseStart_1920198 : Nat := 118140960795 + 1920198 * 2 ^ 59
def prefixEnd_1920198 : Nat := 4983230072969 + 3 ^ 40 * 1920198 * 2
def baseEnd_1920198 : Nat := 146071781600323474102841

theorem tailTrace_1920198 : CollatzResearch.WordTrace tailWord_1920198 prefixEnd_1920198 146071781600323474102841 := by
  unfold tailWord_1920198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2188605459295564517330539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46690249798305376369718165 2188605459295564517330539)
  ·
    refine ⟨3282908188943346775995809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2188605459295564517330539 3282908188943346775995809)
    ·
      refine ⟨2462181141707510081996857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3282908188943346775995809 2462181141707510081996857)
      ·
        refine ⟨1846635856280632561497643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2462181141707510081996857 1846635856280632561497643)
        ·
          refine ⟨2769953784420948842246465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1846635856280632561497643 2769953784420948842246465)
          ·
            refine ⟨2077465338315711631684849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2769953784420948842246465 2077465338315711631684849)
            ·
              refine ⟨1558099003736783723763637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2077465338315711631684849 1558099003736783723763637)
              ·
                refine ⟨146071781600323474102841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1558099003736783723763637 146071781600323474102841)
                ·
                  rfl

theorem cell21_1920198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_1920198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1920198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1920198 prefixEnd_1920198 := by exact prefixLift 1920198
  have htrace : WordTrace (prefixWord ++ tailWord_1920198) baseStart_1920198 baseEnd_1920198 := by
    simpa [prefixWord, tailWord_1920198, baseEnd_1920198] using wordTrace_append hprefix tailTrace_1920198
  have hstable : (prefixWord ++ tailWord_1920198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920198).length < 2 ^ (prefixWord ++ tailWord_1920198).sum := by decide
  have hdescent : baseEnd_1920198 < baseStart_1920198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920203 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 7]
def baseStart_1920203 : Nat := 118140960795 + 1920203 * 2 ^ 59
def prefixEnd_1920203 : Nat := 4983230072969 + 3 ^ 40 * 1920203 * 2
def baseEnd_1920203 : Nat := 438216485869091524725179

theorem tailTrace_1920203 : CollatzResearch.WordTrace tailWord_1920203 prefixEnd_1920203 438216485869091524725179 := by
  unfold tailWord_1920203
  simp only [CollatzResearch.WordTrace]
  refine ⟨70035557062439950408509263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46690371374959966939006175 70035557062439950408509263)
  ·
    refine ⟨105053335593659925612763895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70035557062439950408509263 105053335593659925612763895)
    ·
      refine ⟨157580003390489888419145843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105053335593659925612763895 157580003390489888419145843)
      ·
        refine ⟨236370005085734832628718765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157580003390489888419145843 236370005085734832628718765)
        ·
          refine ⟨88638751907150562235769537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236370005085734832628718765 88638751907150562235769537)
          ·
            refine ⟨66479063930362921676827153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88638751907150562235769537 66479063930362921676827153)
            ·
              refine ⟨49859297947772191257620365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66479063930362921676827153 49859297947772191257620365)
              ·
                refine ⟨18697236730414571721607637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49859297947772191257620365 18697236730414571721607637)
                ·
                  refine ⟨438216485869091524725179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18697236730414571721607637 438216485869091524725179)
                  ·
                    rfl

theorem cell21_1920203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 7].length) (baseStart_1920203 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1920203 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1920203 prefixEnd_1920203 := by exact prefixLift 1920203
  have htrace : WordTrace (prefixWord ++ tailWord_1920203) baseStart_1920203 baseEnd_1920203 := by
    simpa [prefixWord, tailWord_1920203, baseEnd_1920203] using wordTrace_append hprefix tailTrace_1920203
  have hstable : (prefixWord ++ tailWord_1920203).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920203).length < 2 ^ (prefixWord ++ tailWord_1920203).sum := by decide
  have hdescent : baseEnd_1920203 < baseStart_1920203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920206 : List Nat := [4, 1, 1, 1, 5, 1, 1, 7]
def baseStart_1920206 : Nat := 118140960795 + 1920206 * 2 ^ 59
def prefixEnd_1920206 : Nat := 4983230072969 + 3 ^ 40 * 1920206 * 2
def baseEnd_1920206 : Nat := 146072390169988062058391

theorem tailTrace_1920206 : CollatzResearch.WordTrace tailWord_1920206 prefixEnd_1920206 146072390169988062058391 := by
  unfold tailWord_1920206
  simp only [CollatzResearch.WordTrace]
  refine ⟨8754458310178635240108559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46690444320952721280578981 8754458310178635240108559)
  ·
    refine ⟨13131687465267952860162839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8754458310178635240108559 13131687465267952860162839)
    ·
      refine ⟨19697531197901929290244259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13131687465267952860162839 19697531197901929290244259)
      ·
        refine ⟨29546296796852893935366389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19697531197901929290244259 29546296796852893935366389)
        ·
          refine ⟨2769965324704958806440599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29546296796852893935366389 2769965324704958806440599)
          ·
            refine ⟨4154947987057438209660899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2769965324704958806440599 4154947987057438209660899)
            ·
              refine ⟨6232421980586157314491349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4154947987057438209660899 6232421980586157314491349)
              ·
                refine ⟨146072390169988062058391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6232421980586157314491349 146072390169988062058391)
                ·
                  rfl

theorem cell21_1920206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_1920206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1920206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1920206 prefixEnd_1920206 := by exact prefixLift 1920206
  have htrace : WordTrace (prefixWord ++ tailWord_1920206) baseStart_1920206 baseEnd_1920206 := by
    simpa [prefixWord, tailWord_1920206, baseEnd_1920206] using wordTrace_append hprefix tailTrace_1920206
  have hstable : (prefixWord ++ tailWord_1920206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920206).length < 2 ^ (prefixWord ++ tailWord_1920206).sum := by decide
  have hdescent : baseEnd_1920206 < baseStart_1920206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920212 : List Nat := [2, 4, 1, 4, 1, 2, 1, 3, 3]
def baseStart_1920212 : Nat := 118140960795 + 1920212 * 2 ^ 59
def prefixEnd_1920212 : Nat := 4983230072969 + 3 ^ 40 * 1920212 * 2
def baseEnd_1920212 : Nat := 438218539791709509075161

theorem tailTrace_1920212 : CollatzResearch.WordTrace tailWord_1920212 prefixEnd_1920212 438218539791709509075161 := by
  unfold tailWord_1920212
  simp only [CollatzResearch.WordTrace]
  refine ⟨35017942659703672472793445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46690590212938229963724593 35017942659703672472793445)
  ·
    refine ⟨6565864248694438588648771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35017942659703672472793445 6565864248694438588648771)
    ·
      refine ⟨9848796373041657882973157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6565864248694438588648771 9848796373041657882973157)
      ·
        refine ⟨1846649319945310853057467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9848796373041657882973157 1846649319945310853057467)
        ·
          refine ⟨2769973979917966279586201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1846649319945310853057467 2769973979917966279586201)
          ·
            refine ⟨2077480484938474709689651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2769973979917966279586201 2077480484938474709689651)
            ·
              refine ⟨3116220727407712064534477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2077480484938474709689651 3116220727407712064534477)
              ·
                refine ⟨1168582772777892024200429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3116220727407712064534477 1168582772777892024200429)
                ·
                  refine ⟨438218539791709509075161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1168582772777892024200429 438218539791709509075161)
                  ·
                    rfl

theorem cell21_1920212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_1920212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1920212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1920212 prefixEnd_1920212 := by exact prefixLift 1920212
  have htrace : WordTrace (prefixWord ++ tailWord_1920212) baseStart_1920212 baseEnd_1920212 := by
    simpa [prefixWord, tailWord_1920212, baseEnd_1920212] using wordTrace_append hprefix tailTrace_1920212
  have hstable : (prefixWord ++ tailWord_1920212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920212).length < 2 ^ (prefixWord ++ tailWord_1920212).sum := by decide
  have hdescent : baseEnd_1920212 < baseStart_1920212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920237 : List Nat := [1, 5, 1, 2, 2, 1, 3, 1, 5]
def baseStart_1920237 : Nat := 118140960795 + 1920237 * 2 ^ 59
def prefixEnd_1920237 : Nat := 4983230072969 + 3 ^ 40 * 1920237 * 2
def baseEnd_1920237 : Nat := 438224245132315021158443

theorem tailTrace_1920237 : CollatzResearch.WordTrace tailWord_1920237 prefixEnd_1920237 438224245132315021158443 := by
  unfold tailWord_1920237
  simp only [CollatzResearch.WordTrace]
  refine ⟨70036797144316774215246965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46691198096211182810164643 70036797144316774215246965)
  ·
    refine ⟨6565949732279697582679403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70036797144316774215246965 6565949732279697582679403)
    ·
      refine ⟨9848924598419546374019105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6565949732279697582679403 9848924598419546374019105)
      ·
        refine ⟨7386693448814659780514329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9848924598419546374019105 7386693448814659780514329)
        ·
          refine ⟨5540020086610994835385747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7386693448814659780514329 5540020086610994835385747)
          ·
            refine ⟨8310030129916492253078621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5540020086610994835385747 8310030129916492253078621)
            ·
              refine ⟨3116261298718684594904483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8310030129916492253078621 3116261298718684594904483)
              ·
                refine ⟨4674391948078026892356725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3116261298718684594904483 4674391948078026892356725)
                ·
                  refine ⟨438224245132315021158443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4674391948078026892356725 438224245132315021158443)
                  ·
                    rfl

theorem cell21_1920237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_1920237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1920237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1920237 prefixEnd_1920237 := by exact prefixLift 1920237
  have htrace : WordTrace (prefixWord ++ tailWord_1920237) baseStart_1920237 baseEnd_1920237 := by
    simpa [prefixWord, tailWord_1920237, baseEnd_1920237] using wordTrace_append hprefix tailTrace_1920237
  have hstable : (prefixWord ++ tailWord_1920237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920237).length < 2 ^ (prefixWord ++ tailWord_1920237).sum := by decide
  have hdescent : baseEnd_1920237 < baseStart_1920237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920288 : List Nat := [2, 1, 1, 5, 4, 1, 2, 2, 3]
def baseStart_1920288 : Nat := 118140960795 + 1920288 * 2 ^ 59
def prefixEnd_1920288 : Nat := 4983230072969 + 3 ^ 40 * 1920288 * 2
def baseEnd_1920288 : Nat := 438235884027150265808339

theorem tailTrace_1920288 : CollatzResearch.WordTrace tailWord_1920288 prefixEnd_1920288 438235884027150265808339 := by
  unfold tailWord_1920288
  simp only [CollatzResearch.WordTrace]
  refine ⟨35019328633566004962676759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46692438178088006616902345 35019328633566004962676759)
  ·
    refine ⟨52528992950349007444015139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35019328633566004962676759 52528992950349007444015139)
    ·
      refine ⟨78793489425523511166022709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52528992950349007444015139 78793489425523511166022709)
      ·
        refine ⟨7386889633642829171814629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78793489425523511166022709 7386889633642829171814629)
        ·
          refine ⟨1385041806308030469715243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7386889633642829171814629 1385041806308030469715243)
          ·
            refine ⟨2077562709462045704572865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1385041806308030469715243 2077562709462045704572865)
            ·
              refine ⟨1558172032096534278429649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2077562709462045704572865 1558172032096534278429649)
              ·
                refine ⟨1168629024072400708822237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1558172032096534278429649 1168629024072400708822237)
                ·
                  refine ⟨438235884027150265808339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1168629024072400708822237 438235884027150265808339)
                  ·
                    rfl

theorem cell21_1920288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2, 3].length) (baseStart_1920288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1920288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1920288 prefixEnd_1920288 := by exact prefixLift 1920288
  have htrace : WordTrace (prefixWord ++ tailWord_1920288) baseStart_1920288 baseEnd_1920288 := by
    simpa [prefixWord, tailWord_1920288, baseEnd_1920288] using wordTrace_append hprefix tailTrace_1920288
  have hstable : (prefixWord ++ tailWord_1920288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920288).length < 2 ^ (prefixWord ++ tailWord_1920288).sum := by decide
  have hdescent : baseEnd_1920288 < baseStart_1920288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920313 : List Nat := [1, 2, 1, 6, 2, 1, 1, 2, 5]
def baseStart_1920313 : Nat := 118140960795 + 1920313 * 2 ^ 59
def prefixEnd_1920313 : Nat := 4983230072969 + 3 ^ 40 * 1920313 * 2
def baseEnd_1920313 : Nat := 438241589367755777891621

theorem tailTrace_1920313 : CollatzResearch.WordTrace tailWord_1920313 prefixEnd_1920313 438241589367755777891621 := by
  unfold tailWord_1920313
  simp only [CollatzResearch.WordTrace]
  refine ⟨70039569092041439195013593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46693046061360959463342395 70039569092041439195013593)
  ·
    refine ⟨52529676819031079396260195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70039569092041439195013593 52529676819031079396260195)
    ·
      refine ⟨78794515228546619094390293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52529676819031079396260195 78794515228546619094390293)
      ·
        refine ⟨3693492901338122770049545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 78794515228546619094390293 3693492901338122770049545)
        ·
          refine ⟨2770119676003592077537159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3693492901338122770049545 2770119676003592077537159)
          ·
            refine ⟨4155179514005388116305739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2770119676003592077537159 4155179514005388116305739)
            ·
              refine ⟨6232769271008082174458609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4155179514005388116305739 6232769271008082174458609)
              ·
                refine ⟨4674576953256061630843957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6232769271008082174458609 4674576953256061630843957)
                ·
                  refine ⟨438241589367755777891621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4674576953256061630843957 438241589367755777891621)
                  ·
                    rfl

theorem cell21_1920313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 5].length) (baseStart_1920313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1920313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1920313 prefixEnd_1920313 := by exact prefixLift 1920313
  have htrace : WordTrace (prefixWord ++ tailWord_1920313) baseStart_1920313 baseEnd_1920313 := by
    simpa [prefixWord, tailWord_1920313, baseEnd_1920313] using wordTrace_append hprefix tailTrace_1920313
  have hstable : (prefixWord ++ tailWord_1920313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920313).length < 2 ^ (prefixWord ++ tailWord_1920313).sum := by decide
  have hdescent : baseEnd_1920313 < baseStart_1920313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920341 : List Nat := [1, 3, 2, 2, 3, 2, 8]
def baseStart_1920341 : Nat := 118140960795 + 1920341 * 2 ^ 59
def prefixEnd_1920341 : Nat := 4983230072969 + 3 ^ 40 * 1920341 * 2
def baseEnd_1920341 : Nat := 48694219927692661269433

theorem tailTrace_1920341 : CollatzResearch.WordTrace tailWord_1920341 prefixEnd_1920341 48694219927692661269433 := by
  unfold tailWord_1920341
  simp only [CollatzResearch.WordTrace]
  refine ⟨70040590335939999977032877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46693726890626666651355251 70040590335939999977032877)
  ·
    refine ⟨26265221375977499991387329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70040590335939999977032877 26265221375977499991387329)
    ·
      refine ⟨19698916031983124993540497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26265221375977499991387329 19698916031983124993540497)
      ·
        refine ⟨14774187023987343745155373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19698916031983124993540497 14774187023987343745155373)
        ·
          refine ⟨5540320133995253904433265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14774187023987343745155373 5540320133995253904433265)
          ·
            refine ⟨4155240100496440428324949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5540320133995253904433265 4155240100496440428324949)
            ·
              refine ⟨48694219927692661269433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4155240100496440428324949 48694219927692661269433)
              ·
                rfl

theorem cell21_1920341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 8].length) (baseStart_1920341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1920341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1920341 prefixEnd_1920341 := by exact prefixLift 1920341
  have htrace : WordTrace (prefixWord ++ tailWord_1920341) baseStart_1920341 baseEnd_1920341 := by
    simpa [prefixWord, tailWord_1920341, baseEnd_1920341] using wordTrace_append hprefix tailTrace_1920341
  have hstable : (prefixWord ++ tailWord_1920341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920341).length < 2 ^ (prefixWord ++ tailWord_1920341).sum := by decide
  have hdescent : baseEnd_1920341 < baseStart_1920341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920389 : List Nat := [1, 3, 1, 1, 3, 1, 5, 3, 3]
def baseStart_1920389 : Nat := 118140960795 + 1920389 * 2 ^ 59
def prefixEnd_1920389 : Nat := 4983230072969 + 3 ^ 40 * 1920389 * 2
def baseEnd_1920389 : Nat := 438258933603196534624799

theorem tailTrace_1920389 : CollatzResearch.WordTrace tailWord_1920389 prefixEnd_1920389 438258933603196534624799 := by
  unfold tailWord_1920389
  simp only [CollatzResearch.WordTrace]
  refine ⟨70042341039766104174780221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46694894026510736116520147 70042341039766104174780221)
  ·
    refine ⟨26265877889912289065542583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70042341039766104174780221 26265877889912289065542583)
    ·
      refine ⟨39398816834868433598313875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26265877889912289065542583 39398816834868433598313875)
      ·
        refine ⟨59098225252302650397470813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39398816834868433598313875 59098225252302650397470813)
        ·
          refine ⟨22161834469613493899051555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59098225252302650397470813 22161834469613493899051555)
          ·
            refine ⟨33242751704420240848577333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22161834469613493899051555 33242751704420240848577333)
            ·
              refine ⟨3116507972289397579554125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33242751704420240848577333 3116507972289397579554125)
              ·
                refine ⟨1168690489608524092332797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3116507972289397579554125 1168690489608524092332797)
                ·
                  refine ⟨438258933603196534624799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1168690489608524092332797 438258933603196534624799)
                  ·
                    rfl

theorem cell21_1920389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3, 3].length) (baseStart_1920389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1920389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1920389 prefixEnd_1920389 := by exact prefixLift 1920389
  have htrace : WordTrace (prefixWord ++ tailWord_1920389) baseStart_1920389 baseEnd_1920389 := by
    simpa [prefixWord, tailWord_1920389, baseEnd_1920389] using wordTrace_append hprefix tailTrace_1920389
  have hstable : (prefixWord ++ tailWord_1920389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920389).length < 2 ^ (prefixWord ++ tailWord_1920389).sum := by decide
  have hdescent : baseEnd_1920389 < baseStart_1920389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920431 : List Nat := [1, 1, 2, 1, 2, 2, 1, 6, 5]
def baseStart_1920431 : Nat := 118140960795 + 1920431 * 2 ^ 59
def prefixEnd_1920431 : Nat := 4983230072969 + 3 ^ 40 * 1920431 * 2
def baseEnd_1920431 : Nat := 438268518575413794924713

theorem tailTrace_1920431 : CollatzResearch.WordTrace tailWord_1920431 prefixEnd_1920431 438268518575413794924713 := by
  unfold tailWord_1920431
  simp only [CollatzResearch.WordTrace]
  refine ⟨70043872905613945347809147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46695915270409296898539431 70043872905613945347809147)
  ·
    refine ⟨105065809358420918021713721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70043872905613945347809147 105065809358420918021713721)
    ·
      refine ⟨78799357018815688516285291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105065809358420918021713721 78799357018815688516285291)
      ·
        refine ⟨118199035528223532774427937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78799357018815688516285291 118199035528223532774427937)
        ·
          refine ⟨88649276646167649580820953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118199035528223532774427937 88649276646167649580820953)
          ·
            refine ⟨66486957484625737185615715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88649276646167649580820953 66486957484625737185615715)
            ·
              refine ⟨99730436226938605778423573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66486957484625737185615715 99730436226938605778423573)
              ·
                refine ⟨4674864198137747145863605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99730436226938605778423573 4674864198137747145863605)
                ·
                  refine ⟨438268518575413794924713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4674864198137747145863605 438268518575413794924713)
                  ·
                    rfl

theorem cell21_1920431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 5].length) (baseStart_1920431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1920431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1920431 prefixEnd_1920431 := by exact prefixLift 1920431
  have htrace : WordTrace (prefixWord ++ tailWord_1920431) baseStart_1920431 baseEnd_1920431 := by
    simpa [prefixWord, tailWord_1920431, baseEnd_1920431] using wordTrace_append hprefix tailTrace_1920431
  have hstable : (prefixWord ++ tailWord_1920431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920431).length < 2 ^ (prefixWord ++ tailWord_1920431).sum := by decide
  have hdescent : baseEnd_1920431 < baseStart_1920431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920462 : List Nat := [4, 1, 1, 1, 2, 1, 2, 3, 6]
def baseStart_1920462 : Nat := 118140960795 + 1920462 * 2 ^ 59
def prefixEnd_1920462 : Nat := 4983230072969 + 3 ^ 40 * 1920462 * 2
def baseEnd_1920462 : Nat := 438275593197764629907983

theorem tailTrace_1920462 : CollatzResearch.WordTrace tailWord_1920462 prefixEnd_1920462 438275593197764629907983 := by
  unfold tailWord_1920462
  simp only [CollatzResearch.WordTrace]
  refine ⟨8755625446062704705273455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46696669045667758428125093 8755625446062704705273455)
  ·
    refine ⟨13133438169094057057910183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8755625446062704705273455 13133438169094057057910183)
    ·
      refine ⟨19700157253641085586865275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13133438169094057057910183 19700157253641085586865275)
      ·
        refine ⟨29550235880461628380297913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19700157253641085586865275 29550235880461628380297913)
        ·
          refine ⟨22162676910346221285223435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29550235880461628380297913 22162676910346221285223435)
          ·
            refine ⟨33244015365519331927835153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22162676910346221285223435 33244015365519331927835153)
            ·
              refine ⟨24933011524139498945876365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33244015365519331927835153 24933011524139498945876365)
              ·
                refine ⟨9349879321552312104703637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24933011524139498945876365 9349879321552312104703637)
                ·
                  refine ⟨438275593197764629907983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9349879321552312104703637 438275593197764629907983)
                  ·
                    rfl

theorem cell21_1920462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_1920462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1920462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1920462 prefixEnd_1920462 := by exact prefixLift 1920462
  have htrace : WordTrace (prefixWord ++ tailWord_1920462) baseStart_1920462 baseEnd_1920462 := by
    simpa [prefixWord, tailWord_1920462, baseEnd_1920462] using wordTrace_append hprefix tailTrace_1920462
  have hstable : (prefixWord ++ tailWord_1920462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920462).length < 2 ^ (prefixWord ++ tailWord_1920462).sum := by decide
  have hdescent : baseEnd_1920462 < baseStart_1920462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920513 : List Nat := [1, 2, 4, 1, 5, 1, 1, 2, 4]
def baseStart_1920513 : Nat := 118140960795 + 1920513 * 2 ^ 59
def prefixEnd_1920513 : Nat := 4983230072969 + 3 ^ 40 * 1920513 * 2
def baseEnd_1920513 : Nat := 438287232092599874557879

theorem tailTrace_1920513 : CollatzResearch.WordTrace tailWord_1920513 prefixEnd_1920513 438287232092599874557879 := by
  unfold tailWord_1920513
  simp only [CollatzResearch.WordTrace]
  refine ⟨70046863691316873352294193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46697909127544582234862795 70046863691316873352294193)
  ·
    refine ⟨52535147768487655014220645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70046863691316873352294193 52535147768487655014220645)
    ·
      refine ⟨9850340206591435315166371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52535147768487655014220645 9850340206591435315166371)
      ·
        refine ⟨14775510309887152972749557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9850340206591435315166371 14775510309887152972749557)
        ·
          refine ⟨1385204091551920591195271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14775510309887152972749557 1385204091551920591195271)
          ·
            refine ⟨2077806137327880886792907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1385204091551920591195271 2077806137327880886792907)
            ·
              refine ⟨3116709205991821330189361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2077806137327880886792907 3116709205991821330189361)
              ·
                refine ⟨2337531904493865997642021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3116709205991821330189361 2337531904493865997642021)
                ·
                  refine ⟨438287232092599874557879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2337531904493865997642021 438287232092599874557879)
                  ·
                    rfl

theorem cell21_1920513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 4].length) (baseStart_1920513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1920513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1920513 prefixEnd_1920513 := by exact prefixLift 1920513
  have htrace : WordTrace (prefixWord ++ tailWord_1920513) baseStart_1920513 baseEnd_1920513 := by
    simpa [prefixWord, tailWord_1920513, baseEnd_1920513] using wordTrace_append hprefix tailTrace_1920513
  have hstable : (prefixWord ++ tailWord_1920513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920513).length < 2 ^ (prefixWord ++ tailWord_1920513).sum := by decide
  have hdescent : baseEnd_1920513 < baseStart_1920513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920558 : List Nat := [4, 1, 3, 1, 2, 1, 3, 3, 3]
def baseStart_1920558 : Nat := 118140960795 + 1920558 * 2 ^ 59
def prefixEnd_1920558 : Nat := 4983230072969 + 3 ^ 40 * 1920558 * 2
def baseEnd_1920558 : Nat := 438297501705689796307787

theorem tailTrace_1920558 : CollatzResearch.WordTrace tailWord_1920558 prefixEnd_1920558 438297501705689796307787 := by
  unfold tailWord_1920558
  simp only [CollatzResearch.WordTrace]
  refine ⟨8756063122019230754710291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46699003317435897358454885 8756063122019230754710291)
  ·
    refine ⟨13134094683028846132065437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8756063122019230754710291 13134094683028846132065437)
    ·
      refine ⟨4925285506135817299524539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13134094683028846132065437 4925285506135817299524539)
      ·
        refine ⟨7387928259203725949286809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4925285506135817299524539 7387928259203725949286809)
        ·
          refine ⟨5540946194402794461965107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7387928259203725949286809 5540946194402794461965107)
          ·
            refine ⟨8311419291604191692947661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5540946194402794461965107 8311419291604191692947661)
            ·
              refine ⟨3116782234351571884855373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8311419291604191692947661 3116782234351571884855373)
              ·
                refine ⟨1168793337881839456820765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3116782234351571884855373 1168793337881839456820765)
                ·
                  refine ⟨438297501705689796307787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1168793337881839456820765 438297501705689796307787)
                  ·
                    rfl

theorem cell21_1920558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_1920558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1920558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1920558 prefixEnd_1920558 := by exact prefixLift 1920558
  have htrace : WordTrace (prefixWord ++ tailWord_1920558) baseStart_1920558 baseEnd_1920558 := by
    simpa [prefixWord, tailWord_1920558, baseEnd_1920558] using wordTrace_append hprefix tailTrace_1920558
  have hstable : (prefixWord ++ tailWord_1920558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920558).length < 2 ^ (prefixWord ++ tailWord_1920558).sum := by decide
  have hdescent : baseEnd_1920558 < baseStart_1920558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920569 : List Nat := [1, 2, 1, 5, 1, 4, 7]
def baseStart_1920569 : Nat := 118140960795 + 1920569 * 2 ^ 59
def prefixEnd_1920569 : Nat := 4983230072969 + 3 ^ 40 * 1920569 * 2
def baseEnd_1920569 : Nat := 48700001339506246847159

theorem tailTrace_1920569 : CollatzResearch.WordTrace tailWord_1920569 prefixEnd_1920569 48700001339506246847159 := by
  unfold tailWord_1920569
  simp only [CollatzResearch.WordTrace]
  refine ⟨70048906179113994916332761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46699270786075996610888507 70048906179113994916332761)
  ·
    refine ⟨52536679634335496187249571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70048906179113994916332761 52536679634335496187249571)
    ·
      refine ⟨78805019451503244280874357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52536679634335496187249571 78805019451503244280874357)
      ·
        refine ⟨7387970573578429151331971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78805019451503244280874357 7387970573578429151331971)
        ·
          refine ⟨11081955860367643726997957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7387970573578429151331971 11081955860367643726997957)
          ·
            refine ⟨2077866723818933198812117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11081955860367643726997957 2077866723818933198812117)
            ·
              refine ⟨48700001339506246847159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2077866723818933198812117 48700001339506246847159)
              ·
                rfl

theorem cell21_1920569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 7].length) (baseStart_1920569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1920569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1920569 prefixEnd_1920569 := by exact prefixLift 1920569
  have htrace : WordTrace (prefixWord ++ tailWord_1920569) baseStart_1920569 baseEnd_1920569 := by
    simpa [prefixWord, tailWord_1920569, baseEnd_1920569] using wordTrace_append hprefix tailTrace_1920569
  have hstable : (prefixWord ++ tailWord_1920569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920569).length < 2 ^ (prefixWord ++ tailWord_1920569).sum := by decide
  have hdescent : baseEnd_1920569 < baseStart_1920569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920693 : List Nat := [1, 3, 3, 3, 2, 1, 2, 1, 5]
def baseStart_1920693 : Nat := 118140960795 + 1920693 * 2 ^ 59
def prefixEnd_1920693 : Nat := 4983230072969 + 3 ^ 40 * 1920693 * 2
def baseEnd_1920693 : Nat := 438328310544959561557511

theorem tailTrace_1920693 : CollatzResearch.WordTrace tailWord_1920693 prefixEnd_1920693 438328310544959561557511 := by
  unfold tailWord_1920693
  simp only [CollatzResearch.WordTrace]
  refine ⟨70053428830664764093846733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46702285887109842729231155 70053428830664764093846733)
  ·
    refine ⟨26270035811499286535192525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70053428830664764093846733 26270035811499286535192525)
    ·
      refine ⟨9851263429312232450697197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26270035811499286535192525 9851263429312232450697197)
      ·
        refine ⟨3694223785992087169011449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9851263429312232450697197 3694223785992087169011449)
        ·
          refine ⟨2770667839494065376758587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3694223785992087169011449 2770667839494065376758587)
          ·
            refine ⟨4156001759241098065137881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2770667839494065376758587 4156001759241098065137881)
            ·
              refine ⟨3117001319430823548853411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4156001759241098065137881 3117001319430823548853411)
              ·
                refine ⟨4675501979146235323280117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3117001319430823548853411 4675501979146235323280117)
                ·
                  refine ⟨438328310544959561557511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4675501979146235323280117 438328310544959561557511)
                  ·
                    rfl

theorem cell21_1920693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_1920693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1920693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1920693 prefixEnd_1920693 := by exact prefixLift 1920693
  have htrace : WordTrace (prefixWord ++ tailWord_1920693) baseStart_1920693 baseEnd_1920693 := by
    simpa [prefixWord, tailWord_1920693, baseEnd_1920693] using wordTrace_append hprefix tailTrace_1920693
  have hstable : (prefixWord ++ tailWord_1920693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920693).length < 2 ^ (prefixWord ++ tailWord_1920693).sum := by decide
  have hdescent : baseEnd_1920693 < baseStart_1920693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920704 : List Nat := [2, 1, 1, 2, 4, 1, 2, 8]
def baseStart_1920704 : Nat := 118140960795 + 1920704 * 2 ^ 59
def prefixEnd_1920704 : Nat := 4983230072969 + 3 ^ 40 * 1920704 * 2
def baseEnd_1920704 : Nat := 146110273631608662291385

theorem tailTrace_1920704 : CollatzResearch.WordTrace tailWord_1920704 prefixEnd_1920704 146110273631608662291385 := by
  unfold tailWord_1920704
  simp only [CollatzResearch.WordTrace]
  refine ⟨35026915016812456486248583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46702553355749941981664777 35026915016812456486248583)
  ·
    refine ⟨52540372525218684729372875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35026915016812456486248583 52540372525218684729372875)
    ·
      refine ⟨78810558787828027094059313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52540372525218684729372875 78810558787828027094059313)
      ·
        refine ⟨59107919090871020320544485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78810558787828027094059313 59107919090871020320544485)
        ·
          refine ⟨11082734829538316310102091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59107919090871020320544485 11082734829538316310102091)
          ·
            refine ⟨16624102244307474465153137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11082734829538316310102091 16624102244307474465153137)
            ·
              refine ⟨12468076683230605848864853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16624102244307474465153137 12468076683230605848864853)
              ·
                refine ⟨146110273631608662291385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12468076683230605848864853 146110273631608662291385)
                ·
                  rfl

theorem cell21_1920704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 8].length) (baseStart_1920704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1920704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1920704 prefixEnd_1920704 := by exact prefixLift 1920704
  have htrace : WordTrace (prefixWord ++ tailWord_1920704) baseStart_1920704 baseEnd_1920704 := by
    simpa [prefixWord, tailWord_1920704, baseEnd_1920704] using wordTrace_append hprefix tailTrace_1920704
  have hstable : (prefixWord ++ tailWord_1920704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920704).length < 2 ^ (prefixWord ++ tailWord_1920704).sum := by decide
  have hdescent : baseEnd_1920704 < baseStart_1920704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920710 : List Nat := [6, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_1920710 : Nat := 118140960795 + 1920710 * 2 ^ 59
def prefixEnd_1920710 : Nat := 4983230072969 + 3 ^ 40 * 1920710 * 2
def baseEnd_1920710 : Nat := 438332190176571309774143

theorem tailTrace_1920710 : CollatzResearch.WordTrace tailWord_1920710 prefixEnd_1920710 438332190176571309774143 := by
  unfold tailWord_1920710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2189189027237599249912987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46702699247735450664810389 2189189027237599249912987)
  ·
    refine ⟨3283783540856398874869481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2189189027237599249912987 3283783540856398874869481)
    ·
      refine ⟨2462837655642299156152111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3283783540856398874869481 2462837655642299156152111)
      ·
        refine ⟨3694256483463448734228167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2462837655642299156152111 3694256483463448734228167)
        ·
          refine ⟨5541384725195173101342251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3694256483463448734228167 5541384725195173101342251)
          ·
            refine ⟨8312077087792759652013377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5541384725195173101342251 8312077087792759652013377)
            ·
              refine ⟨6234057815844569739010033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8312077087792759652013377 6234057815844569739010033)
              ·
                refine ⟨4675543361883427304257525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6234057815844569739010033 4675543361883427304257525)
                ·
                  refine ⟨438332190176571309774143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4675543361883427304257525 438332190176571309774143)
                  ·
                    rfl

theorem cell21_1920710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_1920710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1920710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1920710 prefixEnd_1920710 := by exact prefixLift 1920710
  have htrace : WordTrace (prefixWord ++ tailWord_1920710) baseStart_1920710 baseEnd_1920710 := by
    simpa [prefixWord, tailWord_1920710, baseEnd_1920710] using wordTrace_append hprefix tailTrace_1920710
  have hstable : (prefixWord ++ tailWord_1920710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920710).length < 2 ^ (prefixWord ++ tailWord_1920710).sum := by decide
  have hdescent : baseEnd_1920710 < baseStart_1920710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920721 : List Nat := [1, 2, 2, 1, 2, 4, 4, 5]
def baseStart_1920721 : Nat := 118140960795 + 1920721 * 2 ^ 59
def prefixEnd_1920721 : Nat := 4983230072969 + 3 ^ 40 * 1920721 * 2
def baseEnd_1920721 : Nat := 146111566842145911696929

theorem tailTrace_1920721 : CollatzResearch.WordTrace tailWord_1920721 prefixEnd_1920721 146111566842145911696929 := by
  unfold tailWord_1920721
  simp only [CollatzResearch.WordTrace]
  refine ⟨70054450074563324875866017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46702966716375549917244011 70054450074563324875866017)
  ·
    refine ⟨52540837555922493656899513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70054450074563324875866017 52540837555922493656899513)
    ·
      refine ⟨39405628166941870242674635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52540837555922493656899513 39405628166941870242674635)
      ·
        refine ⟨59108442250412805364011953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39405628166941870242674635 59108442250412805364011953)
        ·
          refine ⟨44331331687809604023008965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59108442250412805364011953 44331331687809604023008965)
          ·
            refine ⟨8312124691464300754314181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44331331687809604023008965 8312124691464300754314181)
            ·
              refine ⟨1558523379649556391433909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8312124691464300754314181 1558523379649556391433909)
              ·
                refine ⟨146111566842145911696929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1558523379649556391433909 146111566842145911696929)
                ·
                  rfl

theorem cell21_1920721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 5].length) (baseStart_1920721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1920721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1920721 prefixEnd_1920721 := by exact prefixLift 1920721
  have htrace : WordTrace (prefixWord ++ tailWord_1920721) baseStart_1920721 baseEnd_1920721 := by
    simpa [prefixWord, tailWord_1920721, baseEnd_1920721] using wordTrace_append hprefix tailTrace_1920721
  have hstable : (prefixWord ++ tailWord_1920721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920721).length < 2 ^ (prefixWord ++ tailWord_1920721).sum := by decide
  have hdescent : baseEnd_1920721 < baseStart_1920721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920780 : List Nat := [2, 2, 1, 2, 2, 1, 4, 7]
def baseStart_1920780 : Nat := 118140960795 + 1920780 * 2 ^ 59
def prefixEnd_1920780 : Nat := 4983230072969 + 3 ^ 40 * 1920780 * 2
def baseEnd_1920780 : Nat := 146116055043422247869111

theorem tailTrace_1920780 : CollatzResearch.WordTrace tailWord_1920780 prefixEnd_1920780 146116055043422247869111 := by
  unfold tailWord_1920780
  simp only [CollatzResearch.WordTrace]
  refine ⟨35028300990674788976131897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46704401320899718634842529 35028300990674788976131897)
  ·
    refine ⟨26271225743006091732098923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35028300990674788976131897 26271225743006091732098923)
    ·
      refine ⟨39406838614509137598148385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26271225743006091732098923 39406838614509137598148385)
      ·
        refine ⟨29555128960881853198611289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39406838614509137598148385 29555128960881853198611289)
        ·
          refine ⟨22166346720661389898958467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29555128960881853198611289 22166346720661389898958467)
          ·
            refine ⟨33249520080992084848437701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22166346720661389898958467 33249520080992084848437701)
            ·
              refine ⟨6234285015186015909082069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33249520080992084848437701 6234285015186015909082069)
              ·
                refine ⟨146116055043422247869111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6234285015186015909082069 146116055043422247869111)
                ·
                  rfl

theorem cell21_1920780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 7].length) (baseStart_1920780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1920780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1920780 prefixEnd_1920780 := by exact prefixLift 1920780
  have htrace : WordTrace (prefixWord ++ tailWord_1920780) baseStart_1920780 baseEnd_1920780 := by
    simpa [prefixWord, tailWord_1920780, baseEnd_1920780] using wordTrace_append hprefix tailTrace_1920780
  have hstable : (prefixWord ++ tailWord_1920780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920780).length < 2 ^ (prefixWord ++ tailWord_1920780).sum := by decide
  have hdescent : baseEnd_1920780 < baseStart_1920780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920901 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 8]
def baseStart_1920901 : Nat := 118140960795 + 1920901 * 2 ^ 59
def prefixEnd_1920901 : Nat := 4983230072969 + 3 ^ 40 * 1920901 * 2
def baseEnd_1920901 : Nat := 438375778978797422090419

theorem tailTrace_1920901 : CollatzResearch.WordTrace tailWord_1920901 prefixEnd_1920901 438375778978797422090419 := by
  unfold tailWord_1920901
  simp only [CollatzResearch.WordTrace]
  refine ⟨70061015213911215617418557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46707343475940810411612371 70061015213911215617418557)
  ·
    refine ⟨26272880705216705856531959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70061015213911215617418557 26272880705216705856531959)
    ·
      refine ⟨39409321057825058784797939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26272880705216705856531959 39409321057825058784797939)
      ·
        refine ⟨59113981586737588177196909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39409321057825058784797939 59113981586737588177196909)
        ·
          refine ⟨22167743095026595566448841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59113981586737588177196909 22167743095026595566448841)
          ·
            refine ⟨16625807321269946674836631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22167743095026595566448841 16625807321269946674836631)
            ·
              refine ⟨24938710981904920012254947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16625807321269946674836631 24938710981904920012254947)
              ·
                refine ⟨37408066472857380018382421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24938710981904920012254947 37408066472857380018382421)
                ·
                  refine ⟨438375778978797422090419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37408066472857380018382421 438375778978797422090419)
                  ·
                    rfl

theorem cell21_1920901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_1920901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1920901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1920901 prefixEnd_1920901 := by exact prefixLift 1920901
  have htrace : WordTrace (prefixWord ++ tailWord_1920901) baseStart_1920901 baseEnd_1920901 := by
    simpa [prefixWord, tailWord_1920901, baseEnd_1920901] using wordTrace_append hprefix tailTrace_1920901
  have hstable : (prefixWord ++ tailWord_1920901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920901).length < 2 ^ (prefixWord ++ tailWord_1920901).sum := by decide
  have hdescent : baseEnd_1920901 < baseStart_1920901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920932 : List Nat := [2, 3, 1, 2, 1, 3, 1, 8]
def baseStart_1920932 : Nat := 118140960795 + 1920932 * 2 ^ 59
def prefixEnd_1920932 : Nat := 4983230072969 + 3 ^ 40 * 1920932 * 2
def baseEnd_1920932 : Nat := 146127617867049419024563

theorem tailTrace_1920932 : CollatzResearch.WordTrace tailWord_1920932 prefixEnd_1920932 146127617867049419024563 := by
  unfold tailWord_1920932
  simp only [CollatzResearch.WordTrace]
  refine ⟨35031072938399453955898525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46708097251199271941198033 35031072938399453955898525)
  ·
    refine ⟨13136652351899795233461947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35031072938399453955898525 13136652351899795233461947)
    ·
      refine ⟨19704978527849692850192921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13136652351899795233461947 19704978527849692850192921)
      ·
        refine ⟨14778733895887269637644691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19704978527849692850192921 14778733895887269637644691)
        ·
          refine ⟨22168100843830904456467037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14778733895887269637644691 22168100843830904456467037)
          ·
            refine ⟨8313037816436589171175139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22168100843830904456467037 8313037816436589171175139)
            ·
              refine ⟨12469556724654883756762709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8313037816436589171175139 12469556724654883756762709)
              ·
                refine ⟨146127617867049419024563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12469556724654883756762709 146127617867049419024563)
                ·
                  rfl

theorem cell21_1920932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 8].length) (baseStart_1920932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1920932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1920932 prefixEnd_1920932 := by exact prefixLift 1920932
  have htrace : WordTrace (prefixWord ++ tailWord_1920932) baseStart_1920932 baseEnd_1920932 := by
    simpa [prefixWord, tailWord_1920932, baseEnd_1920932] using wordTrace_append hprefix tailTrace_1920932
  have hstable : (prefixWord ++ tailWord_1920932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920932).length < 2 ^ (prefixWord ++ tailWord_1920932).sum := by decide
  have hdescent : baseEnd_1920932 < baseStart_1920932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920935 : List Nat := [1, 1, 6, 1, 2, 2, 1, 3, 4]
def baseStart_1920935 : Nat := 118140960795 + 1920935 * 2 ^ 59
def prefixEnd_1920935 : Nat := 4983230072969 + 3 ^ 40 * 1920935 * 2
def baseEnd_1920935 : Nat := 438383538242020918523683

theorem tailTrace_1920935 : CollatzResearch.WordTrace tailWord_1920935 prefixEnd_1920935 438383538242020918523683 := by
  unfold tailWord_1920935
  simp only [CollatzResearch.WordTrace]
  refine ⟨70062255295788039424156259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46708170197192026282770839 70062255295788039424156259)
  ·
    refine ⟨105093382943682059136234389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70062255295788039424156259 105093382943682059136234389)
    ·
      refine ⟨4926252325485096522010987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 105093382943682059136234389 4926252325485096522010987)
      ·
        refine ⟨7389378488227644783016481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4926252325485096522010987 7389378488227644783016481)
        ·
          refine ⟨5542033866170733587262361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7389378488227644783016481 5542033866170733587262361)
          ·
            refine ⟨4156525399628050190446771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5542033866170733587262361 4156525399628050190446771)
            ·
              refine ⟨6234788099442075285670157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4156525399628050190446771 6234788099442075285670157)
              ·
                refine ⟨2338045537290778232126309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6234788099442075285670157 2338045537290778232126309)
                ·
                  refine ⟨438383538242020918523683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2338045537290778232126309 438383538242020918523683)
                  ·
                    rfl

theorem cell21_1920935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 4].length) (baseStart_1920935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1920935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1920935 prefixEnd_1920935 := by exact prefixLift 1920935
  have htrace : WordTrace (prefixWord ++ tailWord_1920935) baseStart_1920935 baseEnd_1920935 := by
    simpa [prefixWord, tailWord_1920935, baseEnd_1920935] using wordTrace_append hprefix tailTrace_1920935
  have hstable : (prefixWord ++ tailWord_1920935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920935).length < 2 ^ (prefixWord ++ tailWord_1920935).sum := by decide
  have hdescent : baseEnd_1920935 < baseStart_1920935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920966 : List Nat := [6, 1, 3, 11]
def baseStart_1920966 : Nat := 118140960795 + 1920966 * 2 ^ 59
def prefixEnd_1920966 : Nat := 4983230072969 + 3 ^ 40 * 1920966 * 2
def baseEnd_1920966 : Nat := 1804076596149677997971

theorem tailTrace_1920966 : CollatzResearch.WordTrace tailWord_1920966 prefixEnd_1920966 1804076596149677997971 := by
  unfold tailWord_1920966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2189480811208616616204211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46708923972450487812356501 2189480811208616616204211)
  ·
    refine ⟨3284221216812924924306317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2189480811208616616204211 3284221216812924924306317)
    ·
      refine ⟨1231582956304846846614869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3284221216812924924306317 1231582956304846846614869)
      ·
        refine ⟨1804076596149677997971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 1231582956304846846614869 1804076596149677997971)
        ·
          rfl

theorem cell21_1920966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 11].length) (baseStart_1920966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1920966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1920966 prefixEnd_1920966 := by exact prefixLift 1920966
  have htrace : WordTrace (prefixWord ++ tailWord_1920966) baseStart_1920966 baseEnd_1920966 := by
    simpa [prefixWord, tailWord_1920966, baseEnd_1920966] using wordTrace_append hprefix tailTrace_1920966
  have hstable : (prefixWord ++ tailWord_1920966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920966).length < 2 ^ (prefixWord ++ tailWord_1920966).sum := by decide
  have hdescent : baseEnd_1920966 < baseStart_1920966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921014 : List Nat := [5, 1, 1, 1, 4, 1, 2, 3, 3]
def baseStart_1921014 : Nat := 118140960795 + 1921014 * 2 ^ 59
def prefixEnd_1921014 : Nat := 4983230072969 + 3 ^ 40 * 1921014 * 2
def baseEnd_1921014 : Nat := 438401567118334336706855

theorem tailTrace_1921014 : CollatzResearch.WordTrace tailWord_1921014 prefixEnd_1921014 438401567118334336706855 := by
  unfold tailWord_1921014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4379071041406364744767631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46710091108334557277521397 4379071041406364744767631)
  ·
    refine ⟨6568606562109547117151447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4379071041406364744767631 6568606562109547117151447)
    ·
      refine ⟨9852909843164320675727171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6568606562109547117151447 9852909843164320675727171)
      ·
        refine ⟨14779364764746481013590757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9852909843164320675727171 14779364764746481013590757)
        ·
          refine ⟨2771130893389965190048267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14779364764746481013590757 2771130893389965190048267)
          ·
            refine ⟨4156696340084947785072401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2771130893389965190048267 4156696340084947785072401)
            ·
              refine ⟨3117522255063710838804301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4156696340084947785072401 3117522255063710838804301)
              ·
                refine ⟨1169070845648891564551613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3117522255063710838804301 1169070845648891564551613)
                ·
                  refine ⟨438401567118334336706855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1169070845648891564551613 438401567118334336706855)
                  ·
                    rfl

theorem cell21_1921014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_1921014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1921014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1921014 prefixEnd_1921014 := by exact prefixLift 1921014
  have htrace : WordTrace (prefixWord ++ tailWord_1921014) baseStart_1921014 baseEnd_1921014 := by
    simpa [prefixWord, tailWord_1921014, baseEnd_1921014] using wordTrace_append hprefix tailTrace_1921014
  have hstable : (prefixWord ++ tailWord_1921014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921014).length < 2 ^ (prefixWord ++ tailWord_1921014).sum := by decide
  have hdescent : baseEnd_1921014 < baseStart_1921014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921070 : List Nat := [4, 1, 3, 1, 1, 2, 1, 2, 6]
def baseStart_1921070 : Nat := 118140960795 + 1921070 * 2 ^ 59
def prefixEnd_1921070 : Nat := 4983230072969 + 3 ^ 40 * 1921070 * 2
def baseEnd_1921070 : Nat := 438414347081290683773407

theorem tailTrace_1921070 : CollatzResearch.WordTrace tailWord_1921070 prefixEnd_1921070 438414347081290683773407 := by
  unfold tailWord_1921070
  simp only [CollatzResearch.WordTrace]
  refine ⟨8758397393787369685040083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46711452766865971653547109 8758397393787369685040083)
  ·
    refine ⟨13137596090681054527560125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8758397393787369685040083 13137596090681054527560125)
    ·
      refine ⟨4926598534005395447835047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13137596090681054527560125 4926598534005395447835047)
      ·
        refine ⟨7389897801008093171752571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4926598534005395447835047 7389897801008093171752571)
        ·
          refine ⟨11084846701512139757628857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7389897801008093171752571 11084846701512139757628857)
          ·
            refine ⟨8313635026134104818221643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11084846701512139757628857 8313635026134104818221643)
            ·
              refine ⟨12470452539201157227332465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8313635026134104818221643 12470452539201157227332465)
              ·
                refine ⟨9352839404400867920499349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12470452539201157227332465 9352839404400867920499349)
                ·
                  refine ⟨438414347081290683773407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9352839404400867920499349 438414347081290683773407)
                  ·
                    rfl

theorem cell21_1921070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_1921070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1921070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1921070 prefixEnd_1921070 := by exact prefixLift 1921070
  have htrace : WordTrace (prefixWord ++ tailWord_1921070) baseStart_1921070 baseEnd_1921070 := by
    simpa [prefixWord, tailWord_1921070, baseEnd_1921070] using wordTrace_append hprefix tailTrace_1921070
  have hstable : (prefixWord ++ tailWord_1921070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921070).length < 2 ^ (prefixWord ++ tailWord_1921070).sum := by decide
  have hdescent : baseEnd_1921070 < baseStart_1921070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921073 : List Nat := [1, 2, 2, 3, 1, 5, 1, 3, 3]
def baseStart_1921073 : Nat := 118140960795 + 1921073 * 2 ^ 59
def prefixEnd_1921073 : Nat := 4983230072969 + 3 ^ 40 * 1921073 * 2
def baseEnd_1921073 : Nat := 438415031722163345223401

theorem tailTrace_1921073 : CollatzResearch.WordTrace tailWord_1921073 prefixEnd_1921073 438415031722163345223401 := by
  unfold tailWord_1921073
  simp only [CollatzResearch.WordTrace]
  refine ⟨70067288569288088992679873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46711525712858725995119915 70067288569288088992679873)
  ·
    refine ⟨52550466426966066744509905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70067288569288088992679873 52550466426966066744509905)
    ·
      refine ⟨39412849820224550058382429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52550466426966066744509905 39412849820224550058382429)
      ·
        refine ⟨14779818682584206271893411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39412849820224550058382429 14779818682584206271893411)
        ·
          refine ⟨22169728023876309407840117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14779818682584206271893411 22169728023876309407840117)
          ·
            refine ⟨2078412002238404006985011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22169728023876309407840117 2078412002238404006985011)
            ·
              refine ⟨3117618003357606010477517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2078412002238404006985011 3117618003357606010477517)
              ·
                refine ⟨1169106751259102253929069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3117618003357606010477517 1169106751259102253929069)
                ·
                  refine ⟨438415031722163345223401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1169106751259102253929069 438415031722163345223401)
                  ·
                    rfl

theorem cell21_1921073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3, 3].length) (baseStart_1921073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1921073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1921073 prefixEnd_1921073 := by exact prefixLift 1921073
  have htrace : WordTrace (prefixWord ++ tailWord_1921073) baseStart_1921073 baseEnd_1921073 := by
    simpa [prefixWord, tailWord_1921073, baseEnd_1921073] using wordTrace_append hprefix tailTrace_1921073
  have hstable : (prefixWord ++ tailWord_1921073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921073).length < 2 ^ (prefixWord ++ tailWord_1921073).sum := by decide
  have hdescent : baseEnd_1921073 < baseStart_1921073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921101 : List Nat := [1, 6, 1, 1, 1, 1, 4, 6]
def baseStart_1921101 : Nat := 118140960795 + 1921101 * 2 ^ 59
def prefixEnd_1921101 : Nat := 4983230072969 + 3 ^ 40 * 1921101 * 2
def baseEnd_1921101 : Nat := 146140473901213839585559

theorem tailTrace_1921101 : CollatzResearch.WordTrace tailWord_1921101 prefixEnd_1921101 146140473901213839585559 := by
  unfold tailWord_1921101
  simp only [CollatzResearch.WordTrace]
  refine ⟨70068309813186649774699157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46712206542124433183132771 70068309813186649774699157)
  ·
    refine ⟨3284452022493124208189023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70068309813186649774699157 3284452022493124208189023)
    ·
      refine ⟨4926678033739686312283535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3284452022493124208189023 4926678033739686312283535)
      ·
        refine ⟨7390017050609529468425303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4926678033739686312283535 7390017050609529468425303)
        ·
          refine ⟨11085025575914294202637955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7390017050609529468425303 11085025575914294202637955)
          ·
            refine ⟨16627538363871441303956933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11085025575914294202637955 16627538363871441303956933)
            ·
              refine ⟨3117663443225895244491925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16627538363871441303956933 3117663443225895244491925)
              ·
                refine ⟨146140473901213839585559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3117663443225895244491925 146140473901213839585559)
                ·
                  rfl

theorem cell21_1921101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 6].length) (baseStart_1921101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1921101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1921101 prefixEnd_1921101 := by exact prefixLift 1921101
  have htrace : WordTrace (prefixWord ++ tailWord_1921101) baseStart_1921101 baseEnd_1921101 := by
    simpa [prefixWord, tailWord_1921101, baseEnd_1921101] using wordTrace_append hprefix tailTrace_1921101
  have hstable : (prefixWord ++ tailWord_1921101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921101).length < 2 ^ (prefixWord ++ tailWord_1921101).sum := by decide
  have hdescent : baseEnd_1921101 < baseStart_1921101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921143 : List Nat := [1, 1, 3, 1, 1, 14]
def baseStart_1921143 : Nat := 118140960795 + 1921143 * 2 ^ 59
def prefixEnd_1921143 : Nat := 4983230072969 + 3 ^ 40 * 1921143 * 2
def baseEnd_1921143 : Nat := 16238185432439214039133

theorem tailTrace_1921143 : CollatzResearch.WordTrace tailWord_1921143 prefixEnd_1921143 16238185432439214039133 := by
  unfold tailWord_1921143
  simp only [CollatzResearch.WordTrace]
  refine ⟨70069841679034490947728083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46713227786022993965152055 70069841679034490947728083)
  ·
    refine ⟨105104762518551736421592125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70069841679034490947728083 105104762518551736421592125)
    ·
      refine ⟨39414285944456901158097047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105104762518551736421592125 39414285944456901158097047)
      ·
        refine ⟨59121428916685351737145571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39414285944456901158097047 59121428916685351737145571)
        ·
          refine ⟨88682143375028027605718357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59121428916685351737145571 88682143375028027605718357)
          ·
            refine ⟨16238185432439214039133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 88682143375028027605718357 16238185432439214039133)
            ·
              rfl

theorem cell21_1921143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 14].length) (baseStart_1921143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1921143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1921143 prefixEnd_1921143 := by exact prefixLift 1921143
  have htrace : WordTrace (prefixWord ++ tailWord_1921143) baseStart_1921143 baseEnd_1921143 := by
    simpa [prefixWord, tailWord_1921143, baseEnd_1921143] using wordTrace_append hprefix tailTrace_1921143
  have hstable : (prefixWord ++ tailWord_1921143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921143).length < 2 ^ (prefixWord ++ tailWord_1921143).sum := by decide
  have hdescent : baseEnd_1921143 < baseStart_1921143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921149 : List Nat := [1, 4, 1, 1, 3, 2, 4, 2, 3]
def baseStart_1921149 : Nat := 118140960795 + 1921149 * 2 ^ 59
def prefixEnd_1921149 : Nat := 4983230072969 + 3 ^ 40 * 1921149 * 2
def baseEnd_1921149 : Nat := 438432375957604101956579

theorem tailTrace_1921149 : CollatzResearch.WordTrace tailWord_1921149 prefixEnd_1921149 438432375957604101956579 := by
  unfold tailWord_1921149
  simp only [CollatzResearch.WordTrace]
  refine ⟨70070060517012753972446501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46713373678008502648297667 70070060517012753972446501)
  ·
    refine ⟨13138136346939891369833719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70070060517012753972446501 13138136346939891369833719)
    ·
      refine ⟨19707204520409837054750579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13138136346939891369833719 19707204520409837054750579)
      ·
        refine ⟨29560806780614755582125869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19707204520409837054750579 29560806780614755582125869)
        ·
          refine ⟨11085302542730533343297201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29560806780614755582125869 11085302542730533343297201)
          ·
            refine ⟨8313976907047900007472901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11085302542730533343297201 8313976907047900007472901)
            ·
              refine ⟨1558870670071481251401169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8313976907047900007472901 1558870670071481251401169)
              ·
                refine ⟨1169153002553610938550877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1558870670071481251401169 1169153002553610938550877)
                ·
                  refine ⟨438432375957604101956579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1169153002553610938550877 438432375957604101956579)
                  ·
                    rfl

theorem cell21_1921149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_1921149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1921149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1921149 prefixEnd_1921149 := by exact prefixLift 1921149
  have htrace : WordTrace (prefixWord ++ tailWord_1921149) baseStart_1921149 baseEnd_1921149 := by
    simpa [prefixWord, tailWord_1921149, baseEnd_1921149] using wordTrace_append hprefix tailTrace_1921149
  have hstable : (prefixWord ++ tailWord_1921149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921149).length < 2 ^ (prefixWord ++ tailWord_1921149).sum := by decide
  have hdescent : baseEnd_1921149 < baseStart_1921149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921329 : List Nat := [1, 2, 2, 3, 4, 2, 1, 6]
def baseStart_1921329 : Nat := 118140960795 + 1921329 * 2 ^ 59
def prefixEnd_1921329 : Nat := 4983230072969 + 3 ^ 40 * 1921329 * 2
def baseEnd_1921329 : Nat := 146157818136654596318737

theorem tailTrace_1921329 : CollatzResearch.WordTrace tailWord_1921329 prefixEnd_1921329 146157818136654596318737 := by
  unfold tailWord_1921329
  simp only [CollatzResearch.WordTrace]
  refine ⟨70076625656360644713999041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46717750437573763142666027 70076625656360644713999041)
  ·
    refine ⟨52557469242270483535499281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70076625656360644713999041 52557469242270483535499281)
    ·
      refine ⟨39418101931702862651624461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52557469242270483535499281 39418101931702862651624461)
      ·
        refine ⟨14781788224388573494359173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39418101931702862651624461 14781788224388573494359173)
        ·
          refine ⟨2771585292072857530192345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14781788224388573494359173 2771585292072857530192345)
          ·
            refine ⟨2078688969054643147644259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2771585292072857530192345 2078688969054643147644259)
            ·
              refine ⟨3118033453581964721466389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2078688969054643147644259 3118033453581964721466389)
              ·
                refine ⟨146157818136654596318737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3118033453581964721466389 146157818136654596318737)
                ·
                  rfl

theorem cell21_1921329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 6].length) (baseStart_1921329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1921329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1921329 prefixEnd_1921329 := by exact prefixLift 1921329
  have htrace : WordTrace (prefixWord ++ tailWord_1921329) baseStart_1921329 baseEnd_1921329 := by
    simpa [prefixWord, tailWord_1921329, baseEnd_1921329] using wordTrace_append hprefix tailTrace_1921329
  have hstable : (prefixWord ++ tailWord_1921329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921329).length < 2 ^ (prefixWord ++ tailWord_1921329).sum := by decide
  have hdescent : baseEnd_1921329 < baseStart_1921329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921360 : List Nat := [2, 1, 1, 1, 1, 7, 2, 3, 3]
def baseStart_1921360 : Nat := 118140960795 + 1921360 * 2 ^ 59
def prefixEnd_1921360 : Nat := 4983230072969 + 3 ^ 40 * 1921360 * 2
def baseEnd_1921360 : Nat := 438480529032314623939481

theorem tailTrace_1921360 : CollatzResearch.WordTrace tailWord_1921360 prefixEnd_1921360 438480529032314623939481 := by
  unfold tailWord_1921360
  simp only [CollatzResearch.WordTrace]
  refine ⟨35038878159624168504188767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46718504212832224672251689 35038878159624168504188767)
  ·
    refine ⟨52558317239436252756283151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35038878159624168504188767 52558317239436252756283151)
    ·
      refine ⟨78837475859154379134424727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52558317239436252756283151 78837475859154379134424727)
      ·
        refine ⟨118256213788731568701637091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78837475859154379134424727 118256213788731568701637091)
        ·
          refine ⟨177384320683097353052455637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118256213788731568701637091 177384320683097353052455637)
          ·
            refine ⟨4157445016010094212166929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 177384320683097353052455637 4157445016010094212166929)
            ·
              refine ⟨3118083762007570659125197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4157445016010094212166929 3118083762007570659125197)
              ·
                refine ⟨1169281410752838997171949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3118083762007570659125197 1169281410752838997171949)
                ·
                  refine ⟨438480529032314623939481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1169281410752838997171949 438480529032314623939481)
                  ·
                    rfl

theorem cell21_1921360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3, 3].length) (baseStart_1921360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1921360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1921360 prefixEnd_1921360 := by exact prefixLift 1921360
  have htrace : WordTrace (prefixWord ++ tailWord_1921360) baseStart_1921360 baseEnd_1921360 := by
    simpa [prefixWord, tailWord_1921360, baseEnd_1921360] using wordTrace_append hprefix tailTrace_1921360
  have hstable : (prefixWord ++ tailWord_1921360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921360).length < 2 ^ (prefixWord ++ tailWord_1921360).sum := by decide
  have hdescent : baseEnd_1921360 < baseStart_1921360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921405 : List Nat := [1, 4, 1, 1, 2, 5, 2, 5]
def baseStart_1921405 : Nat := 118140960795 + 1921405 * 2 ^ 59
def prefixEnd_1921405 : Nat := 4983230072969 + 3 ^ 40 * 1921405 * 2
def baseEnd_1921405 : Nat := 146163599548468181896463

theorem tailTrace_1921405 : CollatzResearch.WordTrace tailWord_1921405 prefixEnd_1921405 146163599548468181896463 := by
  unfold tailWord_1921405
  simp only [CollatzResearch.WordTrace]
  refine ⟨70079397604085309693765669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46719598402723539795843779 70079397604085309693765669)
  ·
    refine ⟨13139887050765995567581063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70079397604085309693765669 13139887050765995567581063)
    ·
      refine ⟨19709830576148993351371595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13139887050765995567581063 19709830576148993351371595)
      ·
        refine ⟨29564745864223490027057393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19709830576148993351371595 29564745864223490027057393)
        ·
          refine ⟨22173559398167617520293045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29564745864223490027057393 22173559398167617520293045)
          ·
            refine ⟨2078771193578214142527473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22173559398167617520293045 2078771193578214142527473)
            ·
              refine ⟨1559078395183660606895605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2078771193578214142527473 1559078395183660606895605)
              ·
                refine ⟨146163599548468181896463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1559078395183660606895605 146163599548468181896463)
                ·
                  rfl

theorem cell21_1921405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 5].length) (baseStart_1921405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1921405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1921405 prefixEnd_1921405 := by exact prefixLift 1921405
  have htrace : WordTrace (prefixWord ++ tailWord_1921405) baseStart_1921405 baseEnd_1921405 := by
    simpa [prefixWord, tailWord_1921405, baseEnd_1921405] using wordTrace_append hprefix tailTrace_1921405
  have hstable : (prefixWord ++ tailWord_1921405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921405).length < 2 ^ (prefixWord ++ tailWord_1921405).sum := by decide
  have hdescent : baseEnd_1921405 < baseStart_1921405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921433 : List Nat := [1, 2, 1, 2, 1, 4, 2, 4, 4]
def baseStart_1921433 : Nat := 118140960795 + 1921433 * 2 ^ 59
def prefixEnd_1921433 : Nat := 4983230072969 + 3 ^ 40 * 1921433 * 2
def baseEnd_1921433 : Nat := 438497188626882719222665

theorem tailTrace_1921433 : CollatzResearch.WordTrace tailWord_1921433 prefixEnd_1921433 438497188626882719222665 := by
  unfold tailWord_1921433
  simp only [CollatzResearch.WordTrace]
  refine ⟨70080418847983870475784953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46720279231989246983856635 70080418847983870475784953)
  ·
    refine ⟨52560314135987902856838715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70080418847983870475784953 52560314135987902856838715)
    ·
      refine ⟨78840471203981854285258073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52560314135987902856838715 78840471203981854285258073)
      ·
        refine ⟨59130353402986390713943555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78840471203981854285258073 59130353402986390713943555)
        ·
          refine ⟨88695530104479586070915333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59130353402986390713943555 88695530104479586070915333)
          ·
            refine ⟨16630411894589922388296625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88695530104479586070915333 16630411894589922388296625)
            ·
              refine ⟨12472808920942441791222469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16630411894589922388296625 12472808920942441791222469)
              ·
                refine ⟨2338651672676707835854213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12472808920942441791222469 2338651672676707835854213)
                ·
                  refine ⟨438497188626882719222665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2338651672676707835854213 438497188626882719222665)
                  ·
                    rfl

theorem cell21_1921433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 4].length) (baseStart_1921433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1921433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1921433 prefixEnd_1921433 := by exact prefixLift 1921433
  have htrace : WordTrace (prefixWord ++ tailWord_1921433) baseStart_1921433 baseEnd_1921433 := by
    simpa [prefixWord, tailWord_1921433, baseEnd_1921433] using wordTrace_append hprefix tailTrace_1921433
  have hstable : (prefixWord ++ tailWord_1921433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921433).length < 2 ^ (prefixWord ++ tailWord_1921433).sum := by decide
  have hdescent : baseEnd_1921433 < baseStart_1921433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921540 : List Nat := [2, 3, 2, 3, 1, 2, 8]
def baseStart_1921540 : Nat := 118140960795 + 1921540 * 2 ^ 59
def prefixEnd_1921540 : Nat := 4983230072969 + 3 ^ 40 * 1921540 * 2
def baseEnd_1921540 : Nat := 48724623053852701215457

theorem tailTrace_1921540 : CollatzResearch.WordTrace tailWord_1921540 prefixEnd_1921540 48724623053852701215457 := by
  unfold tailWord_1921540
  simp only [CollatzResearch.WordTrace]
  refine ⟨35042160729298113874965037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46722880972397485166620049 35042160729298113874965037)
  ·
    refine ⟨13140810273486792703111889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35042160729298113874965037 13140810273486792703111889)
    ·
      refine ⟨9855607705115094527333917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13140810273486792703111889 9855607705115094527333917)
      ·
        refine ⟨3695852889418160447750219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9855607705115094527333917 3695852889418160447750219)
        ·
          refine ⟨5543779334127240671625329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3695852889418160447750219 5543779334127240671625329)
          ·
            refine ⟨4157834500595430503718997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5543779334127240671625329 4157834500595430503718997)
            ·
              refine ⟨48724623053852701215457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4157834500595430503718997 48724623053852701215457)
              ·
                rfl

theorem cell21_1921540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 8].length) (baseStart_1921540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1921540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1921540 prefixEnd_1921540 := by exact prefixLift 1921540
  have htrace : WordTrace (prefixWord ++ tailWord_1921540) baseStart_1921540 baseEnd_1921540 := by
    simpa [prefixWord, tailWord_1921540, baseEnd_1921540] using wordTrace_append hprefix tailTrace_1921540
  have hstable : (prefixWord ++ tailWord_1921540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921540).length < 2 ^ (prefixWord ++ tailWord_1921540).sum := by decide
  have hdescent : baseEnd_1921540 < baseStart_1921540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921543 : List Nat := [1, 1, 4, 3, 3, 2, 1, 2, 4]
def baseStart_1921543 : Nat := 118140960795 + 1921543 * 2 ^ 59
def prefixEnd_1921543 : Nat := 4983230072969 + 3 ^ 40 * 1921543 * 2
def baseEnd_1921543 : Nat := 438522292125546972389107

theorem tailTrace_1921543 : CollatzResearch.WordTrace tailWord_1921543 prefixEnd_1921543 438522292125546972389107 := by
  unfold tailWord_1921543
  simp only [CollatzResearch.WordTrace]
  refine ⟨70084430877585359262289283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46722953918390239508192855 70084430877585359262289283)
  ·
    refine ⟨105126646316378038893433925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70084430877585359262289283 105126646316378038893433925)
    ·
      refine ⟨19711246184320882292518861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105126646316378038893433925 19711246184320882292518861)
      ·
        refine ⟨7391717319120330859694573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19711246184320882292518861 7391717319120330859694573)
        ·
          refine ⟨2771893994670124072385465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7391717319120330859694573 2771893994670124072385465)
          ·
            refine ⟨2078920496002593054289099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2771893994670124072385465 2078920496002593054289099)
            ·
              refine ⟨3118380744003889581433649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2078920496002593054289099 3118380744003889581433649)
              ·
                refine ⟨2338785558002917186075237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3118380744003889581433649 2338785558002917186075237)
                ·
                  refine ⟨438522292125546972389107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2338785558002917186075237 438522292125546972389107)
                  ·
                    rfl

theorem cell21_1921543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 4].length) (baseStart_1921543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1921543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1921543 prefixEnd_1921543 := by exact prefixLift 1921543
  have htrace : WordTrace (prefixWord ++ tailWord_1921543) baseStart_1921543 baseEnd_1921543 := by
    simpa [prefixWord, tailWord_1921543, baseEnd_1921543] using wordTrace_append hprefix tailTrace_1921543
  have hstable : (prefixWord ++ tailWord_1921543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921543).length < 2 ^ (prefixWord ++ tailWord_1921543).sum := by decide
  have hdescent : baseEnd_1921543 < baseStart_1921543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921644 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 8]
def baseStart_1921644 : Nat := 118140960795 + 1921644 * 2 ^ 59
def prefixEnd_1921644 : Nat := 4983230072969 + 3 ^ 40 * 1921644 * 2
def baseEnd_1921644 : Nat := 438545341701593241205567

theorem tailTrace_1921644 : CollatzResearch.WordTrace tailWord_1921644 prefixEnd_1921644 438545341701593241205567 := by
  unfold tailWord_1921644
  simp only [CollatzResearch.WordTrace]
  refine ⟨35044057325109726755857993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46725409766812969007810657 35044057325109726755857993)
  ·
    refine ⟨26283042993832295066893495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35044057325109726755857993 26283042993832295066893495)
    ·
      refine ⟨39424564490748442600340243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26283042993832295066893495 39424564490748442600340243)
      ·
        refine ⟨59136846736122663900510365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39424564490748442600340243 59136846736122663900510365)
        ·
          refine ⟨22176317526045998962691387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59136846736122663900510365 22176317526045998962691387)
          ·
            refine ⟨33264476289068998444037081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22176317526045998962691387 33264476289068998444037081)
            ·
              refine ⟨24948357216801748833027811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33264476289068998444037081 24948357216801748833027811)
              ·
                refine ⟨37422535825202623249541717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24948357216801748833027811 37422535825202623249541717)
                ·
                  refine ⟨438545341701593241205567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37422535825202623249541717 438545341701593241205567)
                  ·
                    rfl

theorem cell21_1921644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_1921644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1921644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1921644 prefixEnd_1921644 := by exact prefixLift 1921644
  have htrace : WordTrace (prefixWord ++ tailWord_1921644) baseStart_1921644 baseEnd_1921644 := by
    simpa [prefixWord, tailWord_1921644, baseEnd_1921644] using wordTrace_append hprefix tailTrace_1921644
  have hstable : (prefixWord ++ tailWord_1921644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921644).length < 2 ^ (prefixWord ++ tailWord_1921644).sum := by decide
  have hdescent : baseEnd_1921644 < baseStart_1921644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921664 : List Nat := [2, 1, 1, 2, 1, 5, 4, 2, 3]
def baseStart_1921664 : Nat := 118140960795 + 1921664 * 2 ^ 59
def prefixEnd_1921664 : Nat := 4983230072969 + 3 ^ 40 * 1921664 * 2
def baseEnd_1921664 : Nat := 438549905974077650872193

theorem tailTrace_1921664 : CollatzResearch.WordTrace tailWord_1921664 prefixEnd_1921664 438549905974077650872193 := by
  unfold tailWord_1921664
  simp only [CollatzResearch.WordTrace]
  refine ⟨35044422055073498463722023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46725896073431331284962697 35044422055073498463722023)
  ·
    refine ⟨52566633082610247695583035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35044422055073498463722023 52566633082610247695583035)
    ·
      refine ⟨78849949623915371543374553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52566633082610247695583035 78849949623915371543374553)
      ·
        refine ⟨59137462217936528657530915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78849949623915371543374553 59137462217936528657530915)
        ·
          refine ⟨88706193326904792986296373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59137462217936528657530915 88706193326904792986296373)
          ·
            refine ⟨8316205624397324342465285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88706193326904792986296373 8316205624397324342465285)
            ·
              refine ⟨1559288554574498314212241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8316205624397324342465285 1559288554574498314212241)
              ·
                refine ⟨1169466415930873735659181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1559288554574498314212241 1169466415930873735659181)
                ·
                  refine ⟨438549905974077650872193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1169466415930873735659181 438549905974077650872193)
                  ·
                    rfl

theorem cell21_1921664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2, 3].length) (baseStart_1921664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1921664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1921664 prefixEnd_1921664 := by exact prefixLift 1921664
  have htrace : WordTrace (prefixWord ++ tailWord_1921664) baseStart_1921664 baseEnd_1921664 := by
    simpa [prefixWord, tailWord_1921664, baseEnd_1921664] using wordTrace_append hprefix tailTrace_1921664
  have hstable : (prefixWord ++ tailWord_1921664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921664).length < 2 ^ (prefixWord ++ tailWord_1921664).sum := by decide
  have hdescent : baseEnd_1921664 < baseStart_1921664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921751 : List Nat := [1, 1, 3, 2, 1, 5, 1, 7]
def baseStart_1921751 : Nat := 118140960795 + 1921751 * 2 ^ 59
def prefixEnd_1921751 : Nat := 4983230072969 + 3 ^ 40 * 1921751 * 2
def baseEnd_1921751 : Nat := 146189920186461610974005

theorem tailTrace_1921751 : CollatzResearch.WordTrace tailWord_1921751 prefixEnd_1921751 146189920186461610974005 := by
  unfold tailWord_1921751
  simp only [CollatzResearch.WordTrace]
  refine ⟨70092017260831810785861107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46728011507221207190574071 70092017260831810785861107)
  ·
    refine ⟨105138025891247716178791661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70092017260831810785861107 105138025891247716178791661)
    ·
      refine ⟨39426759709217893567046873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105138025891247716178791661 39426759709217893567046873)
      ·
        refine ⟨29570069781913420175285155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39426759709217893567046873 29570069781913420175285155)
        ·
          refine ⟨44355104672870130262927733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29570069781913420175285155 44355104672870130262927733)
          ·
            refine ⟨4158291063081574712149475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44355104672870130262927733 4158291063081574712149475)
            ·
              refine ⟨6237436594622362068224213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4158291063081574712149475 6237436594622362068224213)
              ·
                refine ⟨146189920186461610974005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6237436594622362068224213 146189920186461610974005)
                ·
                  rfl

theorem cell21_1921751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 7].length) (baseStart_1921751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1921751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1921751 prefixEnd_1921751 := by exact prefixLift 1921751
  have htrace : WordTrace (prefixWord ++ tailWord_1921751) baseStart_1921751 baseEnd_1921751 := by
    simpa [prefixWord, tailWord_1921751, baseEnd_1921751] using wordTrace_append hprefix tailTrace_1921751
  have hstable : (prefixWord ++ tailWord_1921751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921751).length < 2 ^ (prefixWord ++ tailWord_1921751).sum := by decide
  have hdescent : baseEnd_1921751 < baseStart_1921751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921768 : List Nat := [2, 1, 4, 1, 4, 2, 7]
def baseStart_1921768 : Nat := 118140960795 + 1921768 * 2 ^ 59
def prefixEnd_1921768 : Nat := 4983230072969 + 3 ^ 40 * 1921768 * 2
def baseEnd_1921768 : Nat := 48730404465666286793183

theorem tailTrace_1921768 : CollatzResearch.WordTrace tailWord_1921768 prefixEnd_1921768 48730404465666286793183 := by
  unfold tailWord_1921768
  simp only [CollatzResearch.WordTrace]
  refine ⟨35046318650885111344614979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46728424867846815126153305 35046318650885111344614979)
  ·
    refine ⟨52569477976327667016922469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35046318650885111344614979 52569477976327667016922469)
    ·
      refine ⟨9856777120561437565672963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52569477976327667016922469 9856777120561437565672963)
      ·
        refine ⟨14785165680842156348509445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9856777120561437565672963 14785165680842156348509445)
        ·
          refine ⟨2772218565157904315345521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14785165680842156348509445 2772218565157904315345521)
          ·
            refine ⟨2079163923868428236509141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2772218565157904315345521 2079163923868428236509141)
            ·
              refine ⟨48730404465666286793183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2079163923868428236509141 48730404465666286793183)
              ·
                rfl

theorem cell21_1921768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 7].length) (baseStart_1921768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1921768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1921768 prefixEnd_1921768 := by exact prefixLift 1921768
  have htrace : WordTrace (prefixWord ++ tailWord_1921768) baseStart_1921768 baseEnd_1921768 := by
    simpa [prefixWord, tailWord_1921768, baseEnd_1921768] using wordTrace_append hprefix tailTrace_1921768
  have hstable : (prefixWord ++ tailWord_1921768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921768).length < 2 ^ (prefixWord ++ tailWord_1921768).sum := by decide
  have hdescent : baseEnd_1921768 < baseStart_1921768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921951 : List Nat := [1, 1, 2, 5, 2, 3, 1, 1, 5]
def baseStart_1921951 : Nat := 118140960795 + 1921951 * 2 ^ 59
def prefixEnd_1921951 : Nat := 4983230072969 + 3 ^ 40 * 1921951 * 2
def baseEnd_1921951 : Nat := 438615403284228929588273

theorem tailTrace_1921951 : CollatzResearch.WordTrace tailWord_1921951 prefixEnd_1921951 438615403284228929588273 := by
  unfold tailWord_1921951
  simp only [CollatzResearch.WordTrace]
  refine ⟨70099311860107244943141707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46732874573404829962094471 70099311860107244943141707)
  ·
    refine ⟨105148967790160867414712561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70099311860107244943141707 105148967790160867414712561)
    ·
      refine ⟨78861725842620650561034421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105148967790160867414712561 78861725842620650561034421)
      ·
        refine ⟨7393286797745685990096977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78861725842620650561034421 7393286797745685990096977)
        ·
          refine ⟨5544965098309264492572733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7393286797745685990096977 5544965098309264492572733)
          ·
            refine ⟨2079361911865974184714775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5544965098309264492572733 2079361911865974184714775)
            ·
              refine ⟨3119042867798961277072163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2079361911865974184714775 3119042867798961277072163)
              ·
                refine ⟨4678564301698441915608245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3119042867798961277072163 4678564301698441915608245)
                ·
                  refine ⟨438615403284228929588273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4678564301698441915608245 438615403284228929588273)
                  ·
                    rfl

theorem cell21_1921951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 5].length) (baseStart_1921951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1921951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1921951 prefixEnd_1921951 := by exact prefixLift 1921951
  have htrace : WordTrace (prefixWord ++ tailWord_1921951) baseStart_1921951 baseEnd_1921951 := by
    simpa [prefixWord, tailWord_1921951, baseEnd_1921951] using wordTrace_append hprefix tailTrace_1921951
  have hstable : (prefixWord ++ tailWord_1921951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921951).length < 2 ^ (prefixWord ++ tailWord_1921951).sum := by decide
  have hdescent : baseEnd_1921951 < baseStart_1921951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922058 : List Nat := [3, 1, 2, 2, 3, 3, 1, 2, 4]
def baseStart_1922058 : Nat := 118140960795 + 1922058 * 2 ^ 59
def prefixEnd_1922058 : Nat := 4983230072969 + 3 ^ 40 * 1922058 * 2
def baseEnd_1922058 : Nat := 438639822142020521304721

theorem tailTrace_1922058 : CollatzResearch.WordTrace tailWord_1922058 prefixEnd_1922058 438639822142020521304721 := by
  unfold tailWord_1922058
  simp only [CollatzResearch.WordTrace]
  refine ⟨17525803617679900554321707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46735476313813068144857885 17525803617679900554321707)
  ·
    refine ⟨26288705426519850831482561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17525803617679900554321707 26288705426519850831482561)
    ·
      refine ⟨19716529069889888123611921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26288705426519850831482561 19716529069889888123611921)
      ·
        refine ⟨14787396802417416092708941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19716529069889888123611921 14787396802417416092708941)
        ·
          refine ⟨5545273800906531034765853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14787396802417416092708941 5545273800906531034765853)
          ·
            refine ⟨2079477675339949138037195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5545273800906531034765853 2079477675339949138037195)
            ·
              refine ⟨3119216513009923707055793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2079477675339949138037195 3119216513009923707055793)
              ·
                refine ⟨2339412384757442780291845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3119216513009923707055793 2339412384757442780291845)
                ·
                  refine ⟨438639822142020521304721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2339412384757442780291845 438639822142020521304721)
                  ·
                    rfl

theorem cell21_1922058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_1922058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1922058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1922058 prefixEnd_1922058 := by exact prefixLift 1922058
  have htrace : WordTrace (prefixWord ++ tailWord_1922058) baseStart_1922058 baseEnd_1922058 := by
    simpa [prefixWord, tailWord_1922058, baseEnd_1922058] using wordTrace_append hprefix tailTrace_1922058
  have hstable : (prefixWord ++ tailWord_1922058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922058).length < 2 ^ (prefixWord ++ tailWord_1922058).sum := by decide
  have hdescent : baseEnd_1922058 < baseStart_1922058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922145 : List Nat := [1, 2, 3, 1, 1, 2, 2, 4, 5]
def baseStart_1922145 : Nat := 118140960795 + 1922145 * 2 ^ 59
def prefixEnd_1922145 : Nat := 4983230072969 + 3 ^ 40 * 1922145 * 2
def baseEnd_1922145 : Nat := 438659676727327703354543

theorem tailTrace_1922145 : CollatzResearch.WordTrace tailWord_1922145 prefixEnd_1922145 438659676727327703354543 := by
  unfold tailWord_1922145
  simp only [CollatzResearch.WordTrace]
  refine ⟨70106387621404416075703889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46737591747602944050469259 70106387621404416075703889)
  ·
    refine ⟨52579790716053312056777917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70106387621404416075703889 52579790716053312056777917)
    ·
      refine ⟨19717421518519992021291719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52579790716053312056777917 19717421518519992021291719)
      ·
        refine ⟨29576132277779988031937579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19717421518519992021291719 29576132277779988031937579)
        ·
          refine ⟨44364198416669982047906369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29576132277779988031937579 44364198416669982047906369)
          ·
            refine ⟨33273148812502486535929777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44364198416669982047906369 33273148812502486535929777)
            ·
              refine ⟨24954861609376864901947333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33273148812502486535929777 24954861609376864901947333)
              ·
                refine ⟨4679036551758162169115125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24954861609376864901947333 4679036551758162169115125)
                ·
                  refine ⟨438659676727327703354543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4679036551758162169115125 438659676727327703354543)
                  ·
                    rfl

theorem cell21_1922145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 5].length) (baseStart_1922145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1922145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1922145 prefixEnd_1922145 := by exact prefixLift 1922145
  have htrace : WordTrace (prefixWord ++ tailWord_1922145) baseStart_1922145 baseEnd_1922145 := by
    simpa [prefixWord, tailWord_1922145, baseEnd_1922145] using wordTrace_append hprefix tailTrace_1922145
  have hstable : (prefixWord ++ tailWord_1922145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922145).length < 2 ^ (prefixWord ++ tailWord_1922145).sum := by decide
  have hdescent : baseEnd_1922145 < baseStart_1922145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922176 : List Nat := [2, 1, 1, 2, 1, 3, 3, 4, 4]
def baseStart_1922176 : Nat := 118140960795 + 1922176 * 2 ^ 59
def prefixEnd_1922176 : Nat := 4983230072969 + 3 ^ 40 * 1922176 * 2
def baseEnd_1922176 : Nat := 438666751349678538337813

theorem tailTrace_1922176 : CollatzResearch.WordTrace tailWord_1922176 prefixEnd_1922176 438666751349678538337813 := by
  unfold tailWord_1922176
  simp only [CollatzResearch.WordTrace]
  refine ⟨35053759142146054185041191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46738345522861405580054921 35053759142146054185041191)
  ·
    refine ⟨52580638713219081277561787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35053759142146054185041191 52580638713219081277561787)
    ·
      refine ⟨78870958069828621916342681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52580638713219081277561787 78870958069828621916342681)
      ·
        refine ⟨59153218552371466437257011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78870958069828621916342681 59153218552371466437257011)
        ·
          refine ⟨88729827828557199655885517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59153218552371466437257011 88729827828557199655885517)
          ·
            refine ⟨33273685435708949870957069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88729827828557199655885517 33273685435708949870957069)
            ·
              refine ⟨12477632038390856201608901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33273685435708949870957069 12477632038390856201608901)
              ·
                refine ⟨2339556007198285537801669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12477632038390856201608901 2339556007198285537801669)
                ·
                  refine ⟨438666751349678538337813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2339556007198285537801669 438666751349678538337813)
                  ·
                    rfl

theorem cell21_1922176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 4].length) (baseStart_1922176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1922176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1922176 prefixEnd_1922176 := by exact prefixLift 1922176
  have htrace : WordTrace (prefixWord ++ tailWord_1922176) baseStart_1922176 baseEnd_1922176 := by
    simpa [prefixWord, tailWord_1922176, baseEnd_1922176] using wordTrace_append hprefix tailTrace_1922176
  have hstable : (prefixWord ++ tailWord_1922176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922176).length < 2 ^ (prefixWord ++ tailWord_1922176).sum := by decide
  have hdescent : baseEnd_1922176 < baseStart_1922176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922238 : List Nat := [4, 2, 1, 1, 3, 1, 1, 3, 5]
def baseStart_1922238 : Nat := 118140960795 + 1922238 * 2 ^ 59
def prefixEnd_1922238 : Nat := 4983230072969 + 3 ^ 40 * 1922238 * 2
def baseEnd_1922238 : Nat := 438680900594380208304353

theorem tailTrace_1922238 : CollatzResearch.WordTrace tailWord_1922238 prefixEnd_1922238 438680900594380208304353 := by
  unfold tailWord_1922238
  simp only [CollatzResearch.WordTrace]
  refine ⟨8763722451258436619854921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46739853073378328639226245 8763722451258436619854921)
  ·
    refine ⟨6572791838443827464891191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8763722451258436619854921 6572791838443827464891191)
    ·
      refine ⟨9859187757665741197336787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6572791838443827464891191 9859187757665741197336787)
      ·
        refine ⟨14788781636498611796005181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9859187757665741197336787 14788781636498611796005181)
        ·
          refine ⟨5545793113686979423501943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14788781636498611796005181 5545793113686979423501943)
          ·
            refine ⟨8318689670530469135252915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5545793113686979423501943 8318689670530469135252915)
            ·
              refine ⟨12478034505795703702879373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8318689670530469135252915 12478034505795703702879373)
              ·
                refine ⟨4679262939673388888579765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12478034505795703702879373 4679262939673388888579765)
                ·
                  refine ⟨438680900594380208304353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4679262939673388888579765 438680900594380208304353)
                  ·
                    rfl

theorem cell21_1922238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_1922238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1922238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1922238 prefixEnd_1922238 := by exact prefixLift 1922238
  have htrace : WordTrace (prefixWord ++ tailWord_1922238) baseStart_1922238 baseEnd_1922238 := by
    simpa [prefixWord, tailWord_1922238, baseEnd_1922238] using wordTrace_append hprefix tailTrace_1922238
  have hstable : (prefixWord ++ tailWord_1922238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922238).length < 2 ^ (prefixWord ++ tailWord_1922238).sum := by decide
  have hdescent : baseEnd_1922238 < baseStart_1922238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922387 : List Nat := [1, 1, 1, 2, 1, 1, 6, 2, 6]
def baseStart_1922387 : Nat := 118140960795 + 1922387 * 2 ^ 59
def prefixEnd_1922387 : Nat := 4983230072969 + 3 ^ 40 * 1922387 * 2
def baseEnd_1922387 : Nat := 438714904424389060320715

theorem tailTrace_1922387 : CollatzResearch.WordTrace tailWord_1922387 prefixEnd_1922387 438714904424389060320715 := by
  unfold tailWord_1922387
  simp only [CollatzResearch.WordTrace]
  refine ⟨70115214086527691406013415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46743476057685127604008943 70115214086527691406013415)
  ·
    refine ⟨105172821129791537109020123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70115214086527691406013415 105172821129791537109020123)
    ·
      refine ⟨157759231694687305663530185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105172821129791537109020123 157759231694687305663530185)
      ·
        refine ⟨118319423771015479247647639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157759231694687305663530185 118319423771015479247647639)
        ·
          refine ⟨177479135656523218871471459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118319423771015479247647639 177479135656523218871471459)
          ·
            refine ⟨266218703484784828307207189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177479135656523218871471459 266218703484784828307207189)
            ·
              refine ⟨12479001725849288826900337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 266218703484784828307207189 12479001725849288826900337)
              ·
                refine ⟨9359251294386966620175253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12479001725849288826900337 9359251294386966620175253)
                ·
                  refine ⟨438714904424389060320715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9359251294386966620175253 438714904424389060320715)
                  ·
                    rfl

theorem cell21_1922387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 6].length) (baseStart_1922387 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1922387 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1922387 prefixEnd_1922387 := by exact prefixLift 1922387
  have htrace : WordTrace (prefixWord ++ tailWord_1922387) baseStart_1922387 baseEnd_1922387 := by
    simpa [prefixWord, tailWord_1922387, baseEnd_1922387] using wordTrace_append hprefix tailTrace_1922387
  have hstable : (prefixWord ++ tailWord_1922387).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922387).length < 2 ^ (prefixWord ++ tailWord_1922387).sum := by decide
  have hdescent : baseEnd_1922387 < baseStart_1922387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922404 : List Nat := [2, 3, 1, 1, 3, 3, 1, 1, 6]
def baseStart_1922404 : Nat := 118140960795 + 1922404 * 2 ^ 59
def prefixEnd_1922404 : Nat := 4983230072969 + 3 ^ 40 * 1922404 * 2
def baseEnd_1922404 : Nat := 438718784056000808537347

theorem tailTrace_1922404 : CollatzResearch.WordTrace tailWord_1922404 prefixEnd_1922404 438718784056000808537347 := by
  unfold tailWord_1922404
  simp only [CollatzResearch.WordTrace]
  refine ⟨35057917063733051654691133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46743889418310735539588177 35057917063733051654691133)
  ·
    refine ⟨13146718898899894370509175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35057917063733051654691133 13146718898899894370509175)
    ·
      refine ⟨19720078348349841555763763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13146718898899894370509175 19720078348349841555763763)
      ·
        refine ⟨29580117522524762333645645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19720078348349841555763763 29580117522524762333645645)
        ·
          refine ⟨11092544070946785875117117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29580117522524762333645645 11092544070946785875117117)
          ·
            refine ⟨4159704026605044703168919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11092544070946785875117117 4159704026605044703168919)
            ·
              refine ⟨6239556039907567054753379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4159704026605044703168919 6239556039907567054753379)
              ·
                refine ⟨9359334059861350582130069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6239556039907567054753379 9359334059861350582130069)
                ·
                  refine ⟨438718784056000808537347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9359334059861350582130069 438718784056000808537347)
                  ·
                    rfl

theorem cell21_1922404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_1922404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1922404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1922404 prefixEnd_1922404 := by exact prefixLift 1922404
  have htrace : WordTrace (prefixWord ++ tailWord_1922404) baseStart_1922404 baseEnd_1922404 := by
    simpa [prefixWord, tailWord_1922404, baseEnd_1922404] using wordTrace_append hprefix tailTrace_1922404
  have hstable : (prefixWord ++ tailWord_1922404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922404).length < 2 ^ (prefixWord ++ tailWord_1922404).sum := by decide
  have hdescent : baseEnd_1922404 < baseStart_1922404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922418 : List Nat := [3, 2, 1, 2, 1, 2, 2, 8]
def baseStart_1922418 : Nat := 118140960795 + 1922418 * 2 ^ 59
def prefixEnd_1922418 : Nat := 4983230072969 + 3 ^ 40 * 1922418 * 2
def baseEnd_1922418 : Nat := 146240659682246631767995

theorem tailTrace_1922418 : CollatzResearch.WordTrace tailWord_1922418 prefixEnd_1922418 146240659682246631767995 := by
  unfold tailWord_1922418
  simp only [CollatzResearch.WordTrace]
  refine ⟨17529086187353845925097977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46744229832943589133594605 17529086187353845925097977)
  ·
    refine ⟨13146814640515384443823483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17529086187353845925097977 13146814640515384443823483)
    ·
      refine ⟨19720221960773076665735225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13146814640515384443823483 19720221960773076665735225)
      ·
        refine ⟨14790166470579807499301419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19720221960773076665735225 14790166470579807499301419)
        ·
          refine ⟨22185249705869711248952129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14790166470579807499301419 22185249705869711248952129)
          ·
            refine ⟨16638937279402283436714097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22185249705869711248952129 16638937279402283436714097)
            ·
              refine ⟨12479202959551712577535573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16638937279402283436714097 12479202959551712577535573)
              ·
                refine ⟨146240659682246631767995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12479202959551712577535573 146240659682246631767995)
                ·
                  rfl

theorem cell21_1922418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 8].length) (baseStart_1922418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1922418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1922418 prefixEnd_1922418 := by exact prefixLift 1922418
  have htrace : WordTrace (prefixWord ++ tailWord_1922418) baseStart_1922418 baseEnd_1922418 := by
    simpa [prefixWord, tailWord_1922418, baseEnd_1922418] using wordTrace_append hprefix tailTrace_1922418
  have hstable : (prefixWord ++ tailWord_1922418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922418).length < 2 ^ (prefixWord ++ tailWord_1922418).sum := by decide
  have hdescent : baseEnd_1922418 < baseStart_1922418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922435 : List Nat := [1, 1, 1, 3, 5, 1, 4, 5]
def baseStart_1922435 : Nat := 118140960795 + 1922435 * 2 ^ 59
def prefixEnd_1922435 : Nat := 4983230072969 + 3 ^ 40 * 1922435 * 2
def baseEnd_1922435 : Nat := 146241952892783881173539

theorem tailTrace_1922435 : CollatzResearch.WordTrace tailWord_1922435 prefixEnd_1922435 146241952892783881173539 := by
  unfold tailWord_1922435
  simp only [CollatzResearch.WordTrace]
  refine ⟨70116964790353795603760759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46744643193569197069173839 70116964790353795603760759)
  ·
    refine ⟨105175447185530693405641139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70116964790353795603760759 105175447185530693405641139)
    ·
      refine ⟨157763170778296040108461709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105175447185530693405641139 157763170778296040108461709)
      ·
        refine ⟨59161189041861015040673141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157763170778296040108461709 59161189041861015040673141)
        ·
          refine ⟨5546361472674470160063107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59161189041861015040673141 5546361472674470160063107)
          ·
            refine ⟨8319542209011705240094661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5546361472674470160063107 8319542209011705240094661)
            ·
              refine ⟨1559914164189694732517749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8319542209011705240094661 1559914164189694732517749)
              ·
                refine ⟨146241952892783881173539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1559914164189694732517749 146241952892783881173539)
                ·
                  rfl

theorem cell21_1922435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 5].length) (baseStart_1922435 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1922435 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1922435 prefixEnd_1922435 := by exact prefixLift 1922435
  have htrace : WordTrace (prefixWord ++ tailWord_1922435) baseStart_1922435 baseEnd_1922435 := by
    simpa [prefixWord, tailWord_1922435, baseEnd_1922435] using wordTrace_append hprefix tailTrace_1922435
  have hstable : (prefixWord ++ tailWord_1922435).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922435).length < 2 ^ (prefixWord ++ tailWord_1922435).sum := by decide
  have hdescent : baseEnd_1922435 < baseStart_1922435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922466 : List Nat := [3, 3, 1, 2, 1, 2, 3, 1, 5]
def baseStart_1922466 : Nat := 118140960795 + 1922466 * 2 ^ 59
def prefixEnd_1922466 : Nat := 4983230072969 + 3 ^ 40 * 1922466 * 2
def baseEnd_1922466 : Nat := 438732933300702478503887

theorem tailTrace_1922466 : CollatzResearch.WordTrace tailWord_1922466 prefixEnd_1922466 438732933300702478503887 := by
  unfold tailWord_1922466
  simp only [CollatzResearch.WordTrace]
  refine ⟨17529523863310371974534813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46745396968827658598759501 17529523863310371974534813)
  ·
    refine ⟨6573571448741389490450555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17529523863310371974534813 6573571448741389490450555)
    ·
      refine ⟨9860357173112084235675833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6573571448741389490450555 9860357173112084235675833)
      ·
        refine ⟨7395267879834063176756875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9860357173112084235675833 7395267879834063176756875)
        ·
          refine ⟨11092901819751094765135313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7395267879834063176756875 11092901819751094765135313)
          ·
            refine ⟨8319676364813321073851485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11092901819751094765135313 8319676364813321073851485)
            ·
              refine ⟨3119878636804995402694307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8319676364813321073851485 3119878636804995402694307)
              ·
                refine ⟨4679817955207493104041461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3119878636804995402694307 4679817955207493104041461)
                ·
                  refine ⟨438732933300702478503887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4679817955207493104041461 438732933300702478503887)
                  ·
                    rfl

theorem cell21_1922466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_1922466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1922466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1922466 prefixEnd_1922466 := by exact prefixLift 1922466
  have htrace : WordTrace (prefixWord ++ tailWord_1922466) baseStart_1922466 baseEnd_1922466 := by
    simpa [prefixWord, tailWord_1922466, baseEnd_1922466] using wordTrace_append hprefix tailTrace_1922466
  have hstable : (prefixWord ++ tailWord_1922466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922466).length < 2 ^ (prefixWord ++ tailWord_1922466).sum := by decide
  have hdescent : baseEnd_1922466 < baseStart_1922466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922472 : List Nat := [2, 1, 6, 1, 3, 1, 2, 1, 4]
def baseStart_1922472 : Nat := 118140960795 + 1922472 * 2 ^ 59
def prefixEnd_1922472 : Nat := 4983230072969 + 3 ^ 40 * 1922472 * 2
def baseEnd_1922472 : Nat := 438734302582447801403875

theorem tailTrace_1922472 : CollatzResearch.WordTrace tailWord_1922472 prefixEnd_1922472 438734302582447801403875 := by
  unfold tailWord_1922472
  simp only [CollatzResearch.WordTrace]
  refine ⟨35059157145609875461428835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46745542860813167281905113 35059157145609875461428835)
  ·
    refine ⟨52588735718414813192143253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35059157145609875461428835 52588735718414813192143253)
    ·
      refine ⟨2465096986800694368381715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52588735718414813192143253 2465096986800694368381715)
      ·
        refine ⟨3697645480201041552572573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2465096986800694368381715 3697645480201041552572573)
        ·
          refine ⟨1386617055075390582214715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3697645480201041552572573 1386617055075390582214715)
          ·
            refine ⟨2079925582613085873322073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386617055075390582214715 2079925582613085873322073)
            ·
              refine ⟨1559944186959814404991555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2079925582613085873322073 1559944186959814404991555)
              ·
                refine ⟨2339916280439721607487333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1559944186959814404991555 2339916280439721607487333)
                ·
                  refine ⟨438734302582447801403875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2339916280439721607487333 438734302582447801403875)
                  ·
                    rfl

theorem cell21_1922472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 4].length) (baseStart_1922472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1922472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1922472 prefixEnd_1922472 := by exact prefixLift 1922472
  have htrace : WordTrace (prefixWord ++ tailWord_1922472) baseStart_1922472 baseEnd_1922472 := by
    simpa [prefixWord, tailWord_1922472, baseEnd_1922472] using wordTrace_append hprefix tailTrace_1922472
  have hstable : (prefixWord ++ tailWord_1922472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922472).length < 2 ^ (prefixWord ++ tailWord_1922472).sum := by decide
  have hdescent : baseEnd_1922472 < baseStart_1922472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922570 : List Nat := [3, 1, 2, 2, 2, 3, 8]
def baseStart_1922570 : Nat := 118140960795 + 1922570 * 2 ^ 59
def prefixEnd_1922570 : Nat := 4983230072969 + 3 ^ 40 * 1922570 * 2
def baseEnd_1922570 : Nat := 48750740835291267641149

theorem tailTrace_1922570 : CollatzResearch.WordTrace tailWord_1922570 prefixEnd_1922570 48750740835291267641149 := by
  unfold tailWord_1922570
  simp only [CollatzResearch.WordTrace]
  refine ⟨17530472161216178414981291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46747925763243142439950109 17530472161216178414981291)
  ·
    refine ⟨26295708241824267622471937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17530472161216178414981291 26295708241824267622471937)
    ·
      refine ⟨19721781181368200716853953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26295708241824267622471937 19721781181368200716853953)
      ·
        refine ⟨14791335886026150537640465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19721781181368200716853953 14791335886026150537640465)
        ·
          refine ⟨11093501914519612903230349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14791335886026150537640465 11093501914519612903230349)
          ·
            refine ⟨4160063217944854838711381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11093501914519612903230349 4160063217944854838711381)
            ·
              refine ⟨48750740835291267641149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4160063217944854838711381 48750740835291267641149)
              ·
                rfl

theorem cell21_1922570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 8].length) (baseStart_1922570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1922570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1922570 prefixEnd_1922570 := by exact prefixLift 1922570
  have htrace : WordTrace (prefixWord ++ tailWord_1922570) baseStart_1922570 baseEnd_1922570 := by
    simpa [prefixWord, tailWord_1922570, baseEnd_1922570] using wordTrace_append hprefix tailTrace_1922570
  have hstable : (prefixWord ++ tailWord_1922570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922570).length < 2 ^ (prefixWord ++ tailWord_1922570).sum := by decide
  have hdescent : baseEnd_1922570 < baseStart_1922570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922615 : List Nat := [1, 1, 3, 1, 2, 4, 1, 2, 6]
def baseStart_1922615 : Nat := 118140960795 + 1922615 * 2 ^ 59
def prefixEnd_1922615 : Nat := 4983230072969 + 3 ^ 40 * 1922615 * 2
def baseEnd_1922615 : Nat := 438766937130711330520249

theorem tailTrace_1922615 : CollatzResearch.WordTrace tailWord_1922615 prefixEnd_1922615 438766937130711330520249 := by
  unfold tailWord_1922615
  simp only [CollatzResearch.WordTrace]
  refine ⟨70123529929701686345313299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46749019953134457563542199 70123529929701686345313299)
  ·
    refine ⟨105185294894552529517969949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70123529929701686345313299 105185294894552529517969949)
    ·
      refine ⟨39444485585457198569238731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105185294894552529517969949 39444485585457198569238731)
      ·
        refine ⟨59166728378185797853858097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39444485585457198569238731 59166728378185797853858097)
        ·
          refine ⟨44375046283639348390393573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59166728378185797853858097 44375046283639348390393573)
          ·
            refine ⟨8320321178182377823198795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44375046283639348390393573 8320321178182377823198795)
            ·
              refine ⟨12480481767273566734798193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8320321178182377823198795 12480481767273566734798193)
              ·
                refine ⟨9360361325455175051098645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12480481767273566734798193 9360361325455175051098645)
                ·
                  refine ⟨438766937130711330520249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9360361325455175051098645 438766937130711330520249)
                  ·
                    rfl

theorem cell21_1922615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 6].length) (baseStart_1922615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1922615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1922615 prefixEnd_1922615 := by exact prefixLift 1922615
  have htrace : WordTrace (prefixWord ++ tailWord_1922615) baseStart_1922615 baseEnd_1922615 := by
    simpa [prefixWord, tailWord_1922615, baseEnd_1922615] using wordTrace_append hprefix tailTrace_1922615
  have hstable : (prefixWord ++ tailWord_1922615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922615).length < 2 ^ (prefixWord ++ tailWord_1922615).sum := by decide
  have hdescent : baseEnd_1922615 < baseStart_1922615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922705 : List Nat := [1, 2, 2, 1, 1, 1, 1, 12]
def baseStart_1922705 : Nat := 118140960795 + 1922705 * 2 ^ 59
def prefixEnd_1922705 : Nat := 4983230072969 + 3 ^ 40 * 1922705 * 2
def baseEnd_1922705 : Nat := 146262492118963724673355

theorem tailTrace_1922705 : CollatzResearch.WordTrace tailWord_1922705 prefixEnd_1922705 146262492118963724673355 := by
  unfold tailWord_1922705
  simp only [CollatzResearch.WordTrace]
  refine ⟨70126812499375631716089569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46751208332917087810726379 70126812499375631716089569)
  ·
    refine ⟨52595109374531723787067177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70126812499375631716089569 52595109374531723787067177)
    ·
      refine ⟨39446332030898792840300383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52595109374531723787067177 39446332030898792840300383)
      ·
        refine ⟨59169498046348189260450575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39446332030898792840300383 59169498046348189260450575)
        ·
          refine ⟨88754247069522283890675863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59169498046348189260450575 88754247069522283890675863)
          ·
            refine ⟨133131370604283425836013795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88754247069522283890675863 133131370604283425836013795)
            ·
              refine ⟨199697055906425138754020693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133131370604283425836013795 199697055906425138754020693)
              ·
                refine ⟨146262492118963724673355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 199697055906425138754020693 146262492118963724673355)
                ·
                  rfl

theorem cell21_1922705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 12].length) (baseStart_1922705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1922705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1922705 prefixEnd_1922705 := by exact prefixLift 1922705
  have htrace : WordTrace (prefixWord ++ tailWord_1922705) baseStart_1922705 baseEnd_1922705 := by
    simpa [prefixWord, tailWord_1922705, baseEnd_1922705] using wordTrace_append hprefix tailTrace_1922705
  have hstable : (prefixWord ++ tailWord_1922705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922705).length < 2 ^ (prefixWord ++ tailWord_1922705).sum := by decide
  have hdescent : baseEnd_1922705 < baseStart_1922705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922742 : List Nat := [5, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_1922742 : Nat := 118140960795 + 1922742 * 2 ^ 59
def prefixEnd_1922742 : Nat := 4983230072969 + 3 ^ 40 * 1922742 * 2
def baseEnd_1922742 : Nat := 438795920260987331903323

theorem tailTrace_1922742 : CollatzResearch.WordTrace tailWord_1922742 prefixEnd_1922742 438795920260987331903323 := by
  unfold tailWord_1922742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4383010125015099189699155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46752108000161058023457653 4383010125015099189699155)
  ·
    refine ⟨6574515187522648784548733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4383010125015099189699155 6574515187522648784548733)
    ·
      refine ⟨2465443195320993294205775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6574515187522648784548733 2465443195320993294205775)
      ·
        refine ⟨3698164792981489941308663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2465443195320993294205775 3698164792981489941308663)
        ·
          refine ⟨5547247189472234911962995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3698164792981489941308663 5547247189472234911962995)
          ·
            refine ⟨8320870784208352367944493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5547247189472234911962995 8320870784208352367944493)
            ·
              refine ⟨3120326544078132137979185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8320870784208352367944493 3120326544078132137979185)
              ·
                refine ⟨2340244908058599103484389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3120326544078132137979185 2340244908058599103484389)
                ·
                  refine ⟨438795920260987331903323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2340244908058599103484389 438795920260987331903323)
                  ·
                    rfl

theorem cell21_1922742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_1922742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1922742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1922742 prefixEnd_1922742 := by exact prefixLift 1922742
  have htrace : WordTrace (prefixWord ++ tailWord_1922742) baseStart_1922742 baseEnd_1922742 := by
    simpa [prefixWord, tailWord_1922742, baseEnd_1922742] using wordTrace_append hprefix tailTrace_1922742
  have hstable : (prefixWord ++ tailWord_1922742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922742).length < 2 ^ (prefixWord ++ tailWord_1922742).sum := by decide
  have hdescent : baseEnd_1922742 < baseStart_1922742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922767 : List Nat := [1, 1, 2, 1, 1, 3, 1, 7, 4]
def baseStart_1922767 : Nat := 118140960795 + 1922767 * 2 ^ 59
def prefixEnd_1922767 : Nat := 4983230072969 + 3 ^ 40 * 1922767 * 2
def baseEnd_1922767 : Nat := 438801625601592843986605

theorem tailTrace_1922767 : CollatzResearch.WordTrace tailWord_1922767 prefixEnd_1922767 438801625601592843986605 := by
  unfold tailWord_1922767
  simp only [CollatzResearch.WordTrace]
  refine ⟨70129073825151016304846555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46752715883434010869897703 70129073825151016304846555)
  ·
    refine ⟨105193610737726524457269833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70129073825151016304846555 105193610737726524457269833)
    ·
      refine ⟨78895208053294893342952375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105193610737726524457269833 78895208053294893342952375)
      ·
        refine ⟨118342812079942340014428563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78895208053294893342952375 118342812079942340014428563)
        ·
          refine ⟨177514218119913510021642845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118342812079942340014428563 177514218119913510021642845)
          ·
            refine ⟨66567831794967566258116067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177514218119913510021642845 66567831794967566258116067)
            ·
              refine ⟨99851747692451349387174101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66567831794967566258116067 99851747692451349387174101)
              ·
                refine ⟨2340275336541828501261893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 99851747692451349387174101 2340275336541828501261893)
                ·
                  refine ⟨438801625601592843986605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2340275336541828501261893 438801625601592843986605)
                  ·
                    rfl

theorem cell21_1922767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 4].length) (baseStart_1922767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1922767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1922767 prefixEnd_1922767 := by exact prefixLift 1922767
  have htrace : WordTrace (prefixWord ++ tailWord_1922767) baseStart_1922767 baseEnd_1922767 := by
    simpa [prefixWord, tailWord_1922767, baseEnd_1922767] using wordTrace_append hprefix tailTrace_1922767
  have hstable : (prefixWord ++ tailWord_1922767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922767).length < 2 ^ (prefixWord ++ tailWord_1922767).sum := by decide
  have hdescent : baseEnd_1922767 < baseStart_1922767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922804 : List Nat := [2, 6, 1, 1, 1, 3, 1, 1, 5]
def baseStart_1922804 : Nat := 118140960795 + 1922804 * 2 ^ 59
def prefixEnd_1922804 : Nat := 4983230072969 + 3 ^ 40 * 1922804 * 2
def baseEnd_1922804 : Nat := 438810069505689001869863

theorem tailTrace_1922804 : CollatzResearch.WordTrace tailWord_1922804 prefixEnd_1922804 438810069505689001869863 := by
  unfold tailWord_1922804
  simp only [CollatzResearch.WordTrace]
  refine ⟨35065211663008485811971733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46753615550677981082628977 35065211663008485811971733)
  ·
    refine ⟨1643681796703522772436175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35065211663008485811971733 1643681796703522772436175)
    ·
      refine ⟨2465522695055284158654263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1643681796703522772436175 2465522695055284158654263)
      ·
        refine ⟨3698284042582926237981395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2465522695055284158654263 3698284042582926237981395)
        ·
          refine ⟨5547426063874389356972093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3698284042582926237981395 5547426063874389356972093)
          ·
            refine ⟨2080284773952896008864535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5547426063874389356972093 2080284773952896008864535)
            ·
              refine ⟨3120427160929344013296803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2080284773952896008864535 3120427160929344013296803)
              ·
                refine ⟨4680640741394016019945205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3120427160929344013296803 4680640741394016019945205)
                ·
                  refine ⟨438810069505689001869863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4680640741394016019945205 438810069505689001869863)
                  ·
                    rfl

theorem cell21_1922804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_1922804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1922804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1922804 prefixEnd_1922804 := by exact prefixLift 1922804
  have htrace : WordTrace (prefixWord ++ tailWord_1922804) baseStart_1922804 baseEnd_1922804 := by
    simpa [prefixWord, tailWord_1922804, baseEnd_1922804] using wordTrace_append hprefix tailTrace_1922804
  have hstable : (prefixWord ++ tailWord_1922804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922804).length < 2 ^ (prefixWord ++ tailWord_1922804).sum := by decide
  have hdescent : baseEnd_1922804 < baseStart_1922804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922860 : List Nat := [2, 2, 1, 1, 1, 6, 2, 2, 4]
def baseStart_1922860 : Nat := 118140960795 + 1922860 * 2 ^ 59
def prefixEnd_1922860 : Nat := 4983230072969 + 3 ^ 40 * 1922860 * 2
def baseEnd_1922860 : Nat := 438822849468645348936415

theorem tailTrace_1922860 : CollatzResearch.WordTrace tailWord_1922860 prefixEnd_1922860 438822849468645348936415 := by
  unfold tailWord_1922860
  simp only [CollatzResearch.WordTrace]
  refine ⟨35066232906907046593991017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46754977209209395458654689 35066232906907046593991017)
  ·
    refine ⟨26299674680180284945493263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35066232906907046593991017 26299674680180284945493263)
    ·
      refine ⟨39449512020270427418239895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26299674680180284945493263 39449512020270427418239895)
      ·
        refine ⟨59174268030405641127359843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39449512020270427418239895 59174268030405641127359843)
        ·
          refine ⟨88761402045608461691039765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59174268030405641127359843 88761402045608461691039765)
          ·
            refine ⟨4160690720887896641767489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 88761402045608461691039765 4160690720887896641767489)
            ·
              refine ⟨3120518040665922481325617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4160690720887896641767489 3120518040665922481325617)
              ·
                refine ⟨2340388530499441860994213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3120518040665922481325617 2340388530499441860994213)
                ·
                  refine ⟨438822849468645348936415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2340388530499441860994213 438822849468645348936415)
                  ·
                    rfl

theorem cell21_1922860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_1922860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1922860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1922860 prefixEnd_1922860 := by exact prefixLift 1922860
  have htrace : WordTrace (prefixWord ++ tailWord_1922860) baseStart_1922860 baseEnd_1922860 := by
    simpa [prefixWord, tailWord_1922860, baseEnd_1922860] using wordTrace_append hprefix tailTrace_1922860
  have hstable : (prefixWord ++ tailWord_1922860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922860).length < 2 ^ (prefixWord ++ tailWord_1922860).sum := by decide
  have hdescent : baseEnd_1922860 < baseStart_1922860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922874 : List Nat := [3, 1, 1, 1, 5, 1, 3, 6]
def baseStart_1922874 : Nat := 118140960795 + 1922874 * 2 ^ 59
def prefixEnd_1922874 : Nat := 4983230072969 + 3 ^ 40 * 1922874 * 2
def baseEnd_1922874 : Nat := 146275348153128145234351

theorem tailTrace_1922874 : CollatzResearch.WordTrace tailWord_1922874 prefixEnd_1922874 146275348153128145234351 := by
  unfold tailWord_1922874
  simp only [CollatzResearch.WordTrace]
  refine ⟨17533244108940843394747919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46755317623842249052661117 17533244108940843394747919)
  ·
    refine ⟨26299866163411265092121879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17533244108940843394747919 26299866163411265092121879)
    ·
      refine ⟨39449799245116897638182819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26299866163411265092121879 39449799245116897638182819)
      ·
        refine ⟨59174698867675346457274229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39449799245116897638182819 59174698867675346457274229)
        ·
          refine ⟨5547628018844563730369459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59174698867675346457274229 5547628018844563730369459)
          ·
            refine ⟨8321442028266845595554189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5547628018844563730369459 8321442028266845595554189)
            ·
              refine ⟨3120540760600067098332821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8321442028266845595554189 3120540760600067098332821)
              ·
                refine ⟨146275348153128145234351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3120540760600067098332821 146275348153128145234351)
                ·
                  rfl

theorem cell21_1922874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 6].length) (baseStart_1922874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1922874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1922874 prefixEnd_1922874 := by exact prefixLift 1922874
  have htrace : WordTrace (prefixWord ++ tailWord_1922874) baseStart_1922874 baseEnd_1922874 := by
    simpa [prefixWord, tailWord_1922874, baseEnd_1922874] using wordTrace_append hprefix tailTrace_1922874
  have hstable : (prefixWord ++ tailWord_1922874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922874).length < 2 ^ (prefixWord ++ tailWord_1922874).sum := by decide
  have hdescent : baseEnd_1922874 < baseStart_1922874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922888 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 7]
def baseStart_1922888 : Nat := 118140960795 + 1922888 * 2 ^ 59
def prefixEnd_1922888 : Nat := 4983230072969 + 3 ^ 40 * 1922888 * 2
def baseEnd_1922888 : Nat := 438829239450123522469691

theorem tailTrace_1922888 : CollatzResearch.WordTrace tailWord_1922888 prefixEnd_1922888 438829239450123522469691 := by
  unfold tailWord_1922888
  simp only [CollatzResearch.WordTrace]
  refine ⟨35066743528856326985000659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46755658038475102646667545 35066743528856326985000659)
  ·
    refine ⟨52600115293284490477500989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35066743528856326985000659 52600115293284490477500989)
    ·
      refine ⟨19725043234981683929062871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52600115293284490477500989 19725043234981683929062871)
      ·
        refine ⟨29587564852472525893594307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19725043234981683929062871 29587564852472525893594307)
        ·
          refine ⟨44381347278708788840391461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29587564852472525893594307 44381347278708788840391461)
          ·
            refine ⟨8321502614757897907573399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44381347278708788840391461 8321502614757897907573399)
            ·
              refine ⟨12482253922136846861360099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8321502614757897907573399 12482253922136846861360099)
              ·
                refine ⟨18723380883205270292040149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12482253922136846861360099 18723380883205270292040149)
                ·
                  refine ⟨438829239450123522469691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18723380883205270292040149 438829239450123522469691)
                  ·
                    rfl

theorem cell21_1922888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 7].length) (baseStart_1922888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1922888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1922888 prefixEnd_1922888 := by exact prefixLift 1922888
  have htrace : WordTrace (prefixWord ++ tailWord_1922888) baseStart_1922888 baseEnd_1922888 := by
    simpa [prefixWord, tailWord_1922888, baseEnd_1922888] using wordTrace_append hprefix tailTrace_1922888
  have hstable : (prefixWord ++ tailWord_1922888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922888).length < 2 ^ (prefixWord ++ tailWord_1922888).sum := by decide
  have hdescent : baseEnd_1922888 < baseStart_1922888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922919 : List Nat := [1, 1, 5, 1, 2, 1, 3, 1, 6]
def baseStart_1922919 : Nat := 118140960795 + 1922919 * 2 ^ 59
def prefixEnd_1922919 : Nat := 4983230072969 + 3 ^ 40 * 1922919 * 2
def baseEnd_1922919 : Nat := 438836314072474357452961

theorem tailTrace_1922919 : CollatzResearch.WordTrace tailWord_1922919 prefixEnd_1922919 438836314072474357452961 := by
  unfold tailWord_1922919
  simp only [CollatzResearch.WordTrace]
  refine ⟨70134617720600346264379811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46756411813733564176253207 70134617720600346264379811)
  ·
    refine ⟨105201926580900519396569717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70134617720600346264379811 105201926580900519396569717)
    ·
      refine ⟨9862680616959423693428411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105201926580900519396569717 9862680616959423693428411)
      ·
        refine ⟨14794020925439135540142617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9862680616959423693428411 14794020925439135540142617)
        ·
          refine ⟨11095515694079351655106963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14794020925439135540142617 11095515694079351655106963)
          ·
            refine ⟨16643273541119027482660445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11095515694079351655106963 16643273541119027482660445)
            ·
              refine ⟨6241227577919635305997667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16643273541119027482660445 6241227577919635305997667)
              ·
                refine ⟨9361841366879452958996501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6241227577919635305997667 9361841366879452958996501)
                ·
                  refine ⟨438836314072474357452961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9361841366879452958996501 438836314072474357452961)
                  ·
                    rfl

theorem cell21_1922919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 6].length) (baseStart_1922919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1922919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1922919 prefixEnd_1922919 := by exact prefixLift 1922919
  have htrace : WordTrace (prefixWord ++ tailWord_1922919) baseStart_1922919 baseEnd_1922919 := by
    simpa [prefixWord, tailWord_1922919, baseEnd_1922919] using wordTrace_append hprefix tailTrace_1922919
  have hstable : (prefixWord ++ tailWord_1922919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922919).length < 2 ^ (prefixWord ++ tailWord_1922919).sum := by decide
  have hdescent : baseEnd_1922919 < baseStart_1922919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922981 : List Nat := [1, 3, 1, 2, 1, 1, 1, 8, 3]
def baseStart_1922981 : Nat := 118140960795 + 1922981 * 2 ^ 59
def prefixEnd_1922981 : Nat := 4983230072969 + 3 ^ 40 * 1922981 * 2
def baseEnd_1922981 : Nat := 438850463317176027419501

theorem tailTrace_1922981 : CollatzResearch.WordTrace tailWord_1922981 prefixEnd_1922981 438850463317176027419501 := by
  unfold tailWord_1922981
  simp only [CollatzResearch.WordTrace]
  refine ⟨70136879046375730853136797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46757919364250487235424531 70136879046375730853136797)
  ·
    refine ⟨26301329642390899069926299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70136879046375730853136797 26301329642390899069926299)
    ·
      refine ⟨39451994463586348604889449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26301329642390899069926299 39451994463586348604889449)
      ·
        refine ⟨29588995847689761453667087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39451994463586348604889449 29588995847689761453667087)
        ·
          refine ⟨44383493771534642180500631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29588995847689761453667087 44383493771534642180500631)
          ·
            refine ⟨66575240657301963270750947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44383493771534642180500631 66575240657301963270750947)
            ·
              refine ⟨99862860985952944906126421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66575240657301963270750947 99862860985952944906126421)
              ·
                refine ⟨1170267902179136073118669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 99862860985952944906126421 1170267902179136073118669)
                ·
                  refine ⟨438850463317176027419501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1170267902179136073118669 438850463317176027419501)
                  ·
                    rfl

theorem cell21_1922981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8, 3].length) (baseStart_1922981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1922981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1922981 prefixEnd_1922981 := by exact prefixLift 1922981
  have htrace : WordTrace (prefixWord ++ tailWord_1922981) baseStart_1922981 baseEnd_1922981 := by
    simpa [prefixWord, tailWord_1922981, baseEnd_1922981] using wordTrace_append hprefix tailTrace_1922981
  have hstable : (prefixWord ++ tailWord_1922981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922981).length < 2 ^ (prefixWord ++ tailWord_1922981).sum := by decide
  have hdescent : baseEnd_1922981 < baseStart_1922981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922984 : List Nat := [2, 1, 6, 2, 1, 1, 2, 6]
def baseStart_1922984 : Nat := 118140960795 + 1922984 * 2 ^ 59
def prefixEnd_1922984 : Nat := 4983230072969 + 3 ^ 40 * 1922984 * 2
def baseEnd_1922984 : Nat := 146283715986016229623165

theorem tailTrace_1922984 : CollatzResearch.WordTrace tailWord_1922984 prefixEnd_1922984 146283715986016229623165 := by
  unfold tailWord_1922984
  simp only [CollatzResearch.WordTrace]
  refine ⟨35068494232682431182748003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46757992310243241576997337 35068494232682431182748003)
  ·
    refine ⟨52602741349023646774122005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35068494232682431182748003 52602741349023646774122005)
    ·
      refine ⟨2465753500735483442536969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52602741349023646774122005 2465753500735483442536969)
      ·
        refine ⟨1849315125551612581902727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2465753500735483442536969 1849315125551612581902727)
        ·
          refine ⟨2773972688327418872854091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1849315125551612581902727 2773972688327418872854091)
          ·
            refine ⟨4160959032491128309281137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2773972688327418872854091 4160959032491128309281137)
            ·
              refine ⟨3120719274368346231960853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4160959032491128309281137 3120719274368346231960853)
              ·
                refine ⟨146283715986016229623165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3120719274368346231960853 146283715986016229623165)
                ·
                  rfl

theorem cell21_1922984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 6].length) (baseStart_1922984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1922984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1922984 prefixEnd_1922984 := by exact prefixLift 1922984
  have htrace : WordTrace (prefixWord ++ tailWord_1922984) baseStart_1922984 baseEnd_1922984 := by
    simpa [prefixWord, tailWord_1922984, baseEnd_1922984] using wordTrace_append hprefix tailTrace_1922984
  have hstable : (prefixWord ++ tailWord_1922984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922984).length < 2 ^ (prefixWord ++ tailWord_1922984).sum := by decide
  have hdescent : baseEnd_1922984 < baseStart_1922984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1922995 : List Nat := [1, 1, 1, 2, 3, 1, 5, 3, 4]
def baseStart_1922995 : Nat := 118140960795 + 1922995 * 2 ^ 59
def prefixEnd_1922995 : Nat := 4983230072969 + 3 ^ 40 * 1922995 * 2
def baseEnd_1922995 : Nat := 438853658307915114186139

theorem tailTrace_1922995 : CollatzResearch.WordTrace tailWord_1922995 prefixEnd_1922995 438853658307915114186139 := by
  unfold tailWord_1922995
  simp only [CollatzResearch.WordTrace]
  refine ⟨70137389668325011244146439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46758259778883340829430959 70137389668325011244146439)
  ·
    refine ⟨105206084502487516866219659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70137389668325011244146439 105206084502487516866219659)
    ·
      refine ⟨157809126753731275299329489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105206084502487516866219659 157809126753731275299329489)
      ·
        refine ⟨118356845065298456474497117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157809126753731275299329489 118356845065298456474497117)
        ·
          refine ⟨44383816899486921177936419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118356845065298456474497117 44383816899486921177936419)
          ·
            refine ⟨66575725349230381766904629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44383816899486921177936419 66575725349230381766904629)
            ·
              refine ⟨6241474251490348290647309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66575725349230381766904629 6241474251490348290647309)
              ·
                refine ⟨2340552844308880608992741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6241474251490348290647309 2340552844308880608992741)
                ·
                  refine ⟨438853658307915114186139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2340552844308880608992741 438853658307915114186139)
                  ·
                    rfl

theorem cell21_1922995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 4].length) (baseStart_1922995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1922995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1922995 prefixEnd_1922995 := by exact prefixLift 1922995
  have htrace : WordTrace (prefixWord ++ tailWord_1922995) baseStart_1922995 baseEnd_1922995 := by
    simpa [prefixWord, tailWord_1922995, baseEnd_1922995] using wordTrace_append hprefix tailTrace_1922995
  have hstable : (prefixWord ++ tailWord_1922995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1922995).length < 2 ^ (prefixWord ++ tailWord_1922995).sum := by decide
  have hdescent : baseEnd_1922995 < baseStart_1922995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1922995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923026 : List Nat := [3, 2, 2, 3, 2, 9]
def baseStart_1923026 : Nat := 118140960795 + 1923026 * 2 ^ 59
def prefixEnd_1923026 : Nat := 4983230072969 + 3 ^ 40 * 1923026 * 2
def baseEnd_1923026 : Nat := 16254101219639479598867

theorem tailTrace_1923026 : CollatzResearch.WordTrace tailWord_1923026 prefixEnd_1923026 16254101219639479598867 := by
  unfold tailWord_1923026
  simp only [CollatzResearch.WordTrace]
  refine ⟨17534630082803175884631233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46759013554141802359016621 17534630082803175884631233)
  ·
    refine ⟨13150972562102381913473425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17534630082803175884631233 13150972562102381913473425)
    ·
      refine ⟨9863229421576786435105069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13150972562102381913473425 9863229421576786435105069)
      ·
        refine ⟨3698711033091294913164401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9863229421576786435105069 3698711033091294913164401)
        ·
          refine ⟨2774033274818471184873301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3698711033091294913164401 2774033274818471184873301)
          ·
            refine ⟨16254101219639479598867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2774033274818471184873301 16254101219639479598867)
            ·
              rfl

theorem cell21_1923026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 9].length) (baseStart_1923026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1923026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1923026 prefixEnd_1923026 := by exact prefixLift 1923026
  have htrace : WordTrace (prefixWord ++ tailWord_1923026) baseStart_1923026 baseEnd_1923026 := by
    simpa [prefixWord, tailWord_1923026, baseEnd_1923026] using wordTrace_append hprefix tailTrace_1923026
  have hstable : (prefixWord ++ tailWord_1923026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923026).length < 2 ^ (prefixWord ++ tailWord_1923026).sum := by decide
  have hdescent : baseEnd_1923026 < baseStart_1923026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923057 : List Nat := [1, 2, 2, 2, 5, 1, 1, 2, 5]
def baseStart_1923057 : Nat := 118140960795 + 1923057 * 2 ^ 59
def prefixEnd_1923057 : Nat := 4983230072969 + 3 ^ 40 * 1923057 * 2
def baseEnd_1923057 : Nat := 438867807552616784152679

theorem tailTrace_1923057 : CollatzResearch.WordTrace tailWord_1923057 prefixEnd_1923057 438867807552616784152679 := by
  unfold tailWord_1923057
  simp only [CollatzResearch.WordTrace]
  refine ⟨70139650994100395832903425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46759767329400263888602283 70139650994100395832903425)
  ·
    refine ⟨52604738245575296874677569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70139650994100395832903425 52604738245575296874677569)
    ·
      refine ⟨39453553684181472656008177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52604738245575296874677569 39453553684181472656008177)
      ·
        refine ⟨29590165263136104492006133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39453553684181472656008177 29590165263136104492006133)
        ·
          refine ⟨2774077993419009796125575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29590165263136104492006133 2774077993419009796125575)
          ·
            refine ⟨4161116990128514694188363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2774077993419009796125575 4161116990128514694188363)
            ·
              refine ⟨6241675485192772041282545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4161116990128514694188363 6241675485192772041282545)
              ·
                refine ⟨4681256613894579030961909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6241675485192772041282545 4681256613894579030961909)
                ·
                  refine ⟨438867807552616784152679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4681256613894579030961909 438867807552616784152679)
                  ·
                    rfl

theorem cell21_1923057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 5].length) (baseStart_1923057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1923057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1923057 prefixEnd_1923057 := by exact prefixLift 1923057
  have htrace : WordTrace (prefixWord ++ tailWord_1923057) baseStart_1923057 baseEnd_1923057 := by
    simpa [prefixWord, tailWord_1923057, baseEnd_1923057] using wordTrace_append hprefix tailTrace_1923057
  have hstable : (prefixWord ++ tailWord_1923057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923057).length < 2 ^ (prefixWord ++ tailWord_1923057).sum := by decide
  have hdescent : baseEnd_1923057 < baseStart_1923057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923105 : List Nat := [1, 2, 3, 2, 4, 1, 3, 1, 4]
def baseStart_1923105 : Nat := 118140960795 + 1923105 * 2 ^ 59
def prefixEnd_1923105 : Nat := 4983230072969 + 3 ^ 40 * 1923105 * 2
def baseEnd_1923105 : Nat := 438878761806579367352581

theorem tailTrace_1923105 : CollatzResearch.WordTrace tailWord_1923105 prefixEnd_1923105 438878761806579367352581 := by
  unfold tailWord_1923105
  simp only [CollatzResearch.WordTrace]
  refine ⟨70141401697926500030650769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46760934465284333353767179 70141401697926500030650769)
  ·
    refine ⟨52606051273444875022988077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70141401697926500030650769 52606051273444875022988077)
    ·
      refine ⟨19727269227541828133620529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52606051273444875022988077 19727269227541828133620529)
      ·
        refine ⟨14795451920656371100215397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19727269227541828133620529 14795451920656371100215397)
        ·
          refine ⟨2774147235123069581290387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14795451920656371100215397 2774147235123069581290387)
          ·
            refine ⟨4161220852684604371935581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2774147235123069581290387 4161220852684604371935581)
            ·
              refine ⟨1560457819756726639475843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4161220852684604371935581 1560457819756726639475843)
              ·
                refine ⟨2340686729635089959213765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1560457819756726639475843 2340686729635089959213765)
                ·
                  refine ⟨438878761806579367352581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2340686729635089959213765 438878761806579367352581)
                  ·
                    rfl

theorem cell21_1923105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 4].length) (baseStart_1923105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1923105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1923105 prefixEnd_1923105 := by exact prefixLift 1923105
  have htrace : WordTrace (prefixWord ++ tailWord_1923105) baseStart_1923105 baseEnd_1923105 := by
    simpa [prefixWord, tailWord_1923105, baseEnd_1923105] using wordTrace_append hprefix tailTrace_1923105
  have hstable : (prefixWord ++ tailWord_1923105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923105).length < 2 ^ (prefixWord ++ tailWord_1923105).sum := by decide
  have hdescent : baseEnd_1923105 < baseStart_1923105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923161 : List Nat := [1, 2, 1, 2, 2, 1, 6, 6]
def baseStart_1923161 : Nat := 118140960795 + 1923161 * 2 ^ 59
def prefixEnd_1923161 : Nat := 4983230072969 + 3 ^ 40 * 1923161 * 2
def baseEnd_1923161 : Nat := 146297180589845238139711

theorem tailTrace_1923161 : CollatzResearch.WordTrace tailWord_1923161 prefixEnd_1923161 146297180589845238139711 := by
  unfold tailWord_1923161
  simp only [CollatzResearch.WordTrace]
  refine ⟨70143444185723621594689337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46762296123815747729792891 70143444185723621594689337)
  ·
    refine ⟨52607583139292716196017003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70143444185723621594689337 52607583139292716196017003)
    ·
      refine ⟨78911374708939074294025505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52607583139292716196017003 78911374708939074294025505)
      ·
        refine ⟨59183531031704305720519129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78911374708939074294025505 59183531031704305720519129)
        ·
          refine ⟨44387648273778229290389347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59183531031704305720519129 44387648273778229290389347)
          ·
            refine ⟨66581472410667343935584021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44387648273778229290389347 66581472410667343935584021)
            ·
              refine ⟨3121006519250031746980501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66581472410667343935584021 3121006519250031746980501)
              ·
                refine ⟨146297180589845238139711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3121006519250031746980501 146297180589845238139711)
                ·
                  rfl

theorem cell21_1923161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 6].length) (baseStart_1923161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1923161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1923161 prefixEnd_1923161 := by exact prefixLift 1923161
  have htrace : WordTrace (prefixWord ++ tailWord_1923161) baseStart_1923161 baseEnd_1923161 := by
    simpa [prefixWord, tailWord_1923161, baseEnd_1923161] using wordTrace_append hprefix tailTrace_1923161
  have hstable : (prefixWord ++ tailWord_1923161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923161).length < 2 ^ (prefixWord ++ tailWord_1923161).sum := by decide
  have hdescent : baseEnd_1923161 < baseStart_1923161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923164 : List Nat := [2, 2, 4, 1, 1, 3, 1, 3, 4]
def baseStart_1923164 : Nat := 118140960795 + 1923164 * 2 ^ 59
def prefixEnd_1923164 : Nat := 4983230072969 + 3 ^ 40 * 1923164 * 2
def baseEnd_1923164 : Nat := 438892226410408375869127

theorem tailTrace_1923164 : CollatzResearch.WordTrace tailWord_1923164 prefixEnd_1923164 438892226410408375869127 := by
  unfold tailWord_1923164
  simp only [CollatzResearch.WordTrace]
  refine ⟨35071776802356376553524273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46762369069808502071365697 35071776802356376553524273)
  ·
    refine ⟨26303832601767282415143205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35071776802356376553524273 26303832601767282415143205)
    ·
      refine ⟨4931968612831365452839351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26303832601767282415143205 4931968612831365452839351)
      ·
        refine ⟨7397952919247048179259027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4931968612831365452839351 7397952919247048179259027)
        ·
          refine ⟨11096929378870572268888541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7397952919247048179259027 11096929378870572268888541)
          ·
            refine ⟨4161348517076464600833203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11096929378870572268888541 4161348517076464600833203)
            ·
              refine ⟨6242022775614696901249805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4161348517076464600833203 6242022775614696901249805)
              ·
                refine ⟨2340758540855511337968677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6242022775614696901249805 2340758540855511337968677)
                ·
                  refine ⟨438892226410408375869127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2340758540855511337968677 438892226410408375869127)
                  ·
                    rfl

theorem cell21_1923164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_1923164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1923164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1923164 prefixEnd_1923164 := by exact prefixLift 1923164
  have htrace : WordTrace (prefixWord ++ tailWord_1923164) baseStart_1923164 baseEnd_1923164 := by
    simpa [prefixWord, tailWord_1923164, baseEnd_1923164] using wordTrace_append hprefix tailTrace_1923164
  have hstable : (prefixWord ++ tailWord_1923164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923164).length < 2 ^ (prefixWord ++ tailWord_1923164).sum := by decide
  have hdescent : baseEnd_1923164 < baseStart_1923164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923209 : List Nat := [1, 2, 1, 1, 4, 2, 3, 4, 3]
def baseStart_1923209 : Nat := 118140960795 + 1923209 * 2 ^ 59
def prefixEnd_1923209 : Nat := 4983230072969 + 3 ^ 40 * 1923209 * 2
def baseEnd_1923209 : Nat := 438902496023498297619035

theorem tailTrace_1923209 : CollatzResearch.WordTrace tailWord_1923209 prefixEnd_1923209 438902496023498297619035 := by
  unfold tailWord_1923209
  simp only [CollatzResearch.WordTrace]
  refine ⟨70145194889549725792436681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46763463259699817194957787 70145194889549725792436681)
  ·
    refine ⟨52608896167162294344327511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70145194889549725792436681 52608896167162294344327511)
    ·
      refine ⟨78913344250743441516491267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52608896167162294344327511 78913344250743441516491267)
      ·
        refine ⟨118370016376115162274736901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78913344250743441516491267 118370016376115162274736901)
        ·
          refine ⟨22194378070521592926513169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118370016376115162274736901 22194378070521592926513169)
          ·
            refine ⟨16645783552891194694884877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22194378070521592926513169 16645783552891194694884877)
            ·
              refine ⟨6242168832334198010581829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16645783552891194694884877 6242168832334198010581829)
              ·
                refine ⟨1170406656062662126984093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6242168832334198010581829 1170406656062662126984093)
                ·
                  refine ⟨438902496023498297619035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1170406656062662126984093 438902496023498297619035)
                  ·
                    rfl

theorem cell21_1923209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4, 3].length) (baseStart_1923209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1923209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1923209 prefixEnd_1923209 := by exact prefixLift 1923209
  have htrace : WordTrace (prefixWord ++ tailWord_1923209) baseStart_1923209 baseEnd_1923209 := by
    simpa [prefixWord, tailWord_1923209, baseEnd_1923209] using wordTrace_append hprefix tailTrace_1923209
  have hstable : (prefixWord ++ tailWord_1923209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923209).length < 2 ^ (prefixWord ++ tailWord_1923209).sum := by decide
  have hdescent : baseEnd_1923209 < baseStart_1923209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923251 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 9]
def baseStart_1923251 : Nat := 118140960795 + 1923251 * 2 ^ 59
def prefixEnd_1923251 : Nat := 4983230072969 + 3 ^ 40 * 1923251 * 2
def baseEnd_1923251 : Nat := 438912080995715557918949

theorem tailTrace_1923251 : CollatzResearch.WordTrace tailWord_1923251 prefixEnd_1923251 438912080995715557918949 := by
  unfold tailWord_1923251
  simp only [CollatzResearch.WordTrace]
  refine ⟨70146726755397566965465607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46764484503598377976977071 70146726755397566965465607)
  ·
    refine ⟨105220090133096350448198411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70146726755397566965465607 105220090133096350448198411)
    ·
      refine ⟨157830135199644525672297617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105220090133096350448198411 157830135199644525672297617)
      ·
        refine ⟨118372601399733394254223213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157830135199644525672297617 118372601399733394254223213)
        ·
          refine ⟨44389725524900022845333705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118372601399733394254223213 44389725524900022845333705)
          ·
            refine ⟨33292294143675017134000279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44389725524900022845333705 33292294143675017134000279)
            ·
              refine ⟨49938441215512525701000419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33292294143675017134000279 49938441215512525701000419)
              ·
                refine ⟨74907661823268788551500629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49938441215512525701000419 74907661823268788551500629)
                ·
                  refine ⟨438912080995715557918949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74907661823268788551500629 438912080995715557918949)
                  ·
                    rfl

theorem cell21_1923251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 9].length) (baseStart_1923251 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1923251 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1923251 prefixEnd_1923251 := by exact prefixLift 1923251
  have htrace : WordTrace (prefixWord ++ tailWord_1923251) baseStart_1923251 baseEnd_1923251 := by
    simpa [prefixWord, tailWord_1923251, baseEnd_1923251] using wordTrace_append hprefix tailTrace_1923251
  have hstable : (prefixWord ++ tailWord_1923251).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923251).length < 2 ^ (prefixWord ++ tailWord_1923251).sum := by decide
  have hdescent : baseEnd_1923251 < baseStart_1923251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923330 : List Nat := [3, 4, 1, 1, 2, 1, 1, 8]
def baseStart_1923330 : Nat := 118140960795 + 1923330 * 2 ^ 59
def prefixEnd_1923330 : Nat := 4983230072969 + 3 ^ 40 * 1923330 * 2
def baseEnd_1923330 : Nat := 146310036624009658700707

theorem tailTrace_1923330 : CollatzResearch.WordTrace tailWord_1923330 prefixEnd_1923330 146310036624009658700707 := by
  unfold tailWord_1923330
  simp only [CollatzResearch.WordTrace]
  refine ⟨17537402030527840864397861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46766405414740908971727629 17537402030527840864397861)
  ·
    refine ⟨3288262880723970162074599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17537402030527840864397861 3288262880723970162074599)
    ·
      refine ⟨4932394321085955243111899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3288262880723970162074599 4932394321085955243111899)
      ·
        refine ⟨7398591481628932864667849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4932394321085955243111899 7398591481628932864667849)
        ·
          refine ⟨5548943611221699648500887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7398591481628932864667849 5548943611221699648500887)
          ·
            refine ⟨8323415416832549472751331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5548943611221699648500887 8323415416832549472751331)
            ·
              refine ⟨12485123125248824209126997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8323415416832549472751331 12485123125248824209126997)
              ·
                refine ⟨146310036624009658700707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12485123125248824209126997 146310036624009658700707)
                ·
                  rfl

theorem cell21_1923330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 8].length) (baseStart_1923330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1923330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1923330 prefixEnd_1923330 := by exact prefixLift 1923330
  have htrace : WordTrace (prefixWord ++ tailWord_1923330) baseStart_1923330 baseEnd_1923330 := by
    simpa [prefixWord, tailWord_1923330, baseEnd_1923330] using wordTrace_append hprefix tailTrace_1923330
  have hstable : (prefixWord ++ tailWord_1923330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923330).length < 2 ^ (prefixWord ++ tailWord_1923330).sum := by decide
  have hdescent : baseEnd_1923330 < baseStart_1923330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923378 : List Nat := [3, 2, 1, 1, 5, 1, 1, 4, 3]
def baseStart_1923378 : Nat := 118140960795 + 1923378 * 2 ^ 59
def prefixEnd_1923378 : Nat := 4983230072969 + 3 ^ 40 * 1923378 * 2
def baseEnd_1923378 : Nat := 438941064125991559302023

theorem tailTrace_1923378 : CollatzResearch.WordTrace tailWord_1923378 prefixEnd_1923378 438941064125991559302023 := by
  unfold tailWord_1923378
  simp only [CollatzResearch.WordTrace]
  refine ⟨17537839706484366913834697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46767572550624978436892525 17537839706484366913834697)
  ·
    refine ⟨13153379779863275185376023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17537839706484366913834697 13153379779863275185376023)
    ·
      refine ⟨19730069669794912778064035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13153379779863275185376023 19730069669794912778064035)
      ·
        refine ⟨29595104504692369167096053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19730069669794912778064035 29595104504692369167096053)
        ·
          refine ⟨2774541047314909609415255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29595104504692369167096053 2774541047314909609415255)
          ·
            refine ⟨4161811570972364414122883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2774541047314909609415255 4161811570972364414122883)
            ·
              refine ⟨6242717356458546621184325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4161811570972364414122883 6242717356458546621184325)
              ·
                refine ⟨1170509504335977491472061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6242717356458546621184325 1170509504335977491472061)
                ·
                  refine ⟨438941064125991559302023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1170509504335977491472061 438941064125991559302023)
                  ·
                    rfl

theorem cell21_1923378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_1923378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1923378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1923378 prefixEnd_1923378 := by exact prefixLift 1923378
  have htrace : WordTrace (prefixWord ++ tailWord_1923378) baseStart_1923378 baseEnd_1923378 := by
    simpa [prefixWord, tailWord_1923378, baseEnd_1923378] using wordTrace_append hprefix tailTrace_1923378
  have hstable : (prefixWord ++ tailWord_1923378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923378).length < 2 ^ (prefixWord ++ tailWord_1923378).sum := by decide
  have hdescent : baseEnd_1923378 < baseStart_1923378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923437 : List Nat := [1, 5, 1, 1, 1, 2, 1, 6, 3]
def baseStart_1923437 : Nat := 118140960795 + 1923437 * 2 ^ 59
def prefixEnd_1923437 : Nat := 4983230072969 + 3 ^ 40 * 1923437 * 2
def baseEnd_1923437 : Nat := 438954528729820567818569

theorem tailTrace_1923437 : CollatzResearch.WordTrace tailWord_1923437 prefixEnd_1923437 438954528729820567818569 := by
  unfold tailWord_1923437
  simp only [CollatzResearch.WordTrace]
  refine ⟨70153510732723720731736565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46769007155149147154491043 70153510732723720731736565)
  ·
    refine ⟨6576891631192848818600303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70153510732723720731736565 6576891631192848818600303)
    ·
      refine ⟨9865337446789273227900455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6576891631192848818600303 9865337446789273227900455)
      ·
        refine ⟨14798006170183909841850683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9865337446789273227900455 14798006170183909841850683)
        ·
          refine ⟨22197009255275864762776025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14798006170183909841850683 22197009255275864762776025)
          ·
            refine ⟨16647756941456898572082019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22197009255275864762776025 16647756941456898572082019)
            ·
              refine ⟨24971635412185347858123029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16647756941456898572082019 24971635412185347858123029)
              ·
                refine ⟨1170545409946188180849517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24971635412185347858123029 1170545409946188180849517)
                ·
                  refine ⟨438954528729820567818569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1170545409946188180849517 438954528729820567818569)
                  ·
                    rfl

theorem cell21_1923437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_1923437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1923437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1923437 prefixEnd_1923437 := by exact prefixLift 1923437
  have htrace : WordTrace (prefixWord ++ tailWord_1923437) baseStart_1923437 baseEnd_1923437 := by
    simpa [prefixWord, tailWord_1923437, baseEnd_1923437] using wordTrace_append hprefix tailTrace_1923437
  have hstable : (prefixWord ++ tailWord_1923437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923437).length < 2 ^ (prefixWord ++ tailWord_1923437).sum := by decide
  have hdescent : baseEnd_1923437 < baseStart_1923437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923465 : List Nat := [1, 2, 1, 1, 6, 2, 1, 7]
def baseStart_1923465 : Nat := 118140960795 + 1923465 * 2 ^ 59
def prefixEnd_1923465 : Nat := 4983230072969 + 3 ^ 40 * 1923465 * 2
def baseEnd_1923465 : Nat := 146320306237099580450615

theorem tailTrace_1923465 : CollatzResearch.WordTrace tailWord_1923465 prefixEnd_1923465 146320306237099580450615 := by
  unfold tailWord_1923465
  simp only [CollatzResearch.WordTrace]
  refine ⟨70154531976622281513755849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46769687984414854342503899 70154531976622281513755849)
  ·
    refine ⟨52615898982466711135316887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70154531976622281513755849 52615898982466711135316887)
    ·
      refine ⟨78923848473700066702975331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52615898982466711135316887 78923848473700066702975331)
      ·
        refine ⟨118385772710550100054462997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78923848473700066702975331 118385772710550100054462997)
        ·
          refine ⟨5549333095807035940052953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 118385772710550100054462997 5549333095807035940052953)
          ·
            refine ⟨4161999821855276955039715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5549333095807035940052953 4161999821855276955039715)
            ·
              refine ⟨6242999732782915432559573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4161999821855276955039715 6242999732782915432559573)
              ·
                refine ⟨146320306237099580450615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6242999732782915432559573 146320306237099580450615)
                ·
                  rfl

theorem cell21_1923465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 7].length) (baseStart_1923465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1923465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1923465 prefixEnd_1923465 := by exact prefixLift 1923465
  have htrace : WordTrace (prefixWord ++ tailWord_1923465) baseStart_1923465 baseEnd_1923465 := by
    simpa [prefixWord, tailWord_1923465, baseEnd_1923465] using wordTrace_append hprefix tailTrace_1923465
  have hstable : (prefixWord ++ tailWord_1923465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923465).length < 2 ^ (prefixWord ++ tailWord_1923465).sum := by decide
  have hdescent : baseEnd_1923465 < baseStart_1923465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923479 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 7]
def baseStart_1923479 : Nat := 118140960795 + 1923479 * 2 ^ 59
def prefixEnd_1923479 : Nat := 4983230072969 + 3 ^ 40 * 1923479 * 2
def baseEnd_1923479 : Nat := 438964113702037828118483

theorem tailTrace_1923479 : CollatzResearch.WordTrace tailWord_1923479 prefixEnd_1923479 438964113702037828118483 := by
  unfold tailWord_1923479
  simp only [CollatzResearch.WordTrace]
  refine ⟨70155042598571561904765491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46770028399047707936510327 70155042598571561904765491)
  ·
    refine ⟨105232563897857342857148237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70155042598571561904765491 105232563897857342857148237)
    ·
      refine ⟨39462211461696503571430589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105232563897857342857148237 39462211461696503571430589)
      ·
        refine ⟨14798329298136188839286471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39462211461696503571430589 14798329298136188839286471)
        ·
          refine ⟨22197493947204283258929707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14798329298136188839286471 22197493947204283258929707)
          ·
            refine ⟨33296240920806424888394561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22197493947204283258929707 33296240920806424888394561)
            ·
              refine ⟨24972180690604818666295921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33296240920806424888394561 24972180690604818666295921)
              ·
                refine ⟨18729135517953613999721941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24972180690604818666295921 18729135517953613999721941)
                ·
                  refine ⟨438964113702037828118483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18729135517953613999721941 438964113702037828118483)
                  ·
                    rfl

theorem cell21_1923479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 7].length) (baseStart_1923479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1923479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1923479 prefixEnd_1923479 := by exact prefixLift 1923479
  have htrace : WordTrace (prefixWord ++ tailWord_1923479) baseStart_1923479 baseEnd_1923479 := by
    simpa [prefixWord, tailWord_1923479, baseEnd_1923479] using wordTrace_append hprefix tailTrace_1923479
  have hstable : (prefixWord ++ tailWord_1923479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923479).length < 2 ^ (prefixWord ++ tailWord_1923479).sum := by decide
  have hdescent : baseEnd_1923479 < baseStart_1923479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923662 : List Nat := [4, 1, 1, 1, 1, 2, 4, 1, 6]
def baseStart_1923662 : Nat := 118140960795 + 1923662 * 2 ^ 59
def prefixEnd_1923662 : Nat := 4983230072969 + 3 ^ 40 * 1923662 * 2
def baseEnd_1923662 : Nat := 439005876795270176568109

theorem tailTrace_1923662 : CollatzResearch.WordTrace tailWord_1923662 prefixEnd_1923662 439005876795270176568109 := by
  unfold tailWord_1923662
  simp only [CollatzResearch.WordTrace]
  refine ⟨8770214644613573019834655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46774478104605722772451493 8770214644613573019834655)
  ·
    refine ⟨13155321966920359529751983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8770214644613573019834655 13155321966920359529751983)
    ·
      refine ⟨19732982950380539294627975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13155321966920359529751983 19732982950380539294627975)
      ·
        refine ⟨29599474425570808941941963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19732982950380539294627975 29599474425570808941941963)
        ·
          refine ⟨44399211638356213412912945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29599474425570808941941963 44399211638356213412912945)
          ·
            refine ⟨33299408728767160059684709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44399211638356213412912945 33299408728767160059684709)
            ·
              refine ⟨6243639136643842511190883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33299408728767160059684709 6243639136643842511190883)
              ·
                refine ⟨9365458704965763766786325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6243639136643842511190883 9365458704965763766786325)
                ·
                  refine ⟨439005876795270176568109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9365458704965763766786325 439005876795270176568109)
                  ·
                    rfl

theorem cell21_1923662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_1923662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1923662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1923662 prefixEnd_1923662 := by exact prefixLift 1923662
  have htrace : WordTrace (prefixWord ++ tailWord_1923662) baseStart_1923662 baseEnd_1923662 := by
    simpa [prefixWord, tailWord_1923662, baseEnd_1923662] using wordTrace_append hprefix tailTrace_1923662
  have hstable : (prefixWord ++ tailWord_1923662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923662).length < 2 ^ (prefixWord ++ tailWord_1923662).sum := by decide
  have hdescent : baseEnd_1923662 < baseStart_1923662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923693 : List Nat := [1, 5, 1, 1, 3, 1, 2, 7]
def baseStart_1923693 : Nat := 118140960795 + 1923693 * 2 ^ 59
def prefixEnd_1923693 : Nat := 4983230072969 + 3 ^ 40 * 1923693 * 2
def baseEnd_1923693 : Nat := 146337650472540337183793

theorem tailTrace_1923693 : CollatzResearch.WordTrace tailWord_1923693 prefixEnd_1923693 146337650472540337183793 := by
  unfold tailWord_1923693
  simp only [CollatzResearch.WordTrace]
  refine ⟨70162847819796276453055733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46775231879864184302037155 70162847819796276453055733)
  ·
    refine ⟨6577766983105900917473975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70162847819796276453055733 6577766983105900917473975)
    ·
      refine ⟨9866650474658851376210963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6577766983105900917473975 9866650474658851376210963)
      ·
        refine ⟨14799975711988277064316445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9866650474658851376210963 14799975711988277064316445)
        ·
          refine ⟨5549990891995603899118667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14799975711988277064316445 5549990891995603899118667)
          ·
            refine ⟨8324986337993405848678001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5549990891995603899118667 8324986337993405848678001)
            ·
              refine ⟨6243739753495054386508501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8324986337993405848678001 6243739753495054386508501)
              ·
                refine ⟨146337650472540337183793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6243739753495054386508501 146337650472540337183793)
                ·
                  rfl

theorem cell21_1923693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 7].length) (baseStart_1923693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1923693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1923693 prefixEnd_1923693 := by exact prefixLift 1923693
  have htrace : WordTrace (prefixWord ++ tailWord_1923693) baseStart_1923693 baseEnd_1923693 := by
    simpa [prefixWord, tailWord_1923693, baseEnd_1923693] using wordTrace_append hprefix tailTrace_1923693
  have hstable : (prefixWord ++ tailWord_1923693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923693).length < 2 ^ (prefixWord ++ tailWord_1923693).sum := by decide
  have hdescent : baseEnd_1923693 < baseStart_1923693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923758 : List Nat := [4, 1, 4, 1, 1, 1, 1, 5, 3]
def baseStart_1923758 : Nat := 118140960795 + 1923758 * 2 ^ 59
def prefixEnd_1923758 : Nat := 4983230072969 + 3 ^ 40 * 1923758 * 2
def baseEnd_1923758 : Nat := 439027785303195342967913

theorem tailTrace_1923758 : CollatzResearch.WordTrace tailWord_1923758 prefixEnd_1923758 439027785303195342967913 := by
  unfold tailWord_1923758
  simp only [CollatzResearch.WordTrace]
  refine ⟨8770652320570099069271491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46776812376373861702781285 8770652320570099069271491)
  ·
    refine ⟨13155978480855148603907237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8770652320570099069271491 13155978480855148603907237)
    ·
      refine ⟨2466745965160340363232607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13155978480855148603907237 2466745965160340363232607)
      ·
        refine ⟨3700118947740510544848911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2466745965160340363232607 3700118947740510544848911)
        ·
          refine ⟨5550178421610765817273367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3700118947740510544848911 5550178421610765817273367)
          ·
            refine ⟨8325267632416148725910051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5550178421610765817273367 8325267632416148725910051)
            ·
              refine ⟨12487901448624223088865077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8325267632416148725910051 12487901448624223088865077)
              ·
                refine ⟨1170740760808520914581101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12487901448624223088865077 1170740760808520914581101)
                ·
                  refine ⟨439027785303195342967913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1170740760808520914581101 439027785303195342967913)
                  ·
                    rfl

theorem cell21_1923758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_1923758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1923758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1923758 prefixEnd_1923758 := by exact prefixLift 1923758
  have htrace : WordTrace (prefixWord ++ tailWord_1923758) baseStart_1923758 baseEnd_1923758 := by
    simpa [prefixWord, tailWord_1923758, baseEnd_1923758] using wordTrace_append hprefix tailTrace_1923758
  have hstable : (prefixWord ++ tailWord_1923758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923758).length < 2 ^ (prefixWord ++ tailWord_1923758).sum := by decide
  have hdescent : baseEnd_1923758 < baseStart_1923758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923848 : List Nat := [2, 1, 3, 2, 2, 4, 2, 1, 4]
def baseStart_1923848 : Nat := 118140960795 + 1923848 * 2 ^ 59
def prefixEnd_1923848 : Nat := 4983230072969 + 3 ^ 40 * 1923848 * 2
def baseEnd_1923848 : Nat := 439048324529375186467729

theorem tailTrace_1923848 : CollatzResearch.WordTrace tailWord_1923848 prefixEnd_1923848 439048324529375186467729 := by
  unfold tailWord_1923848
  simp only [CollatzResearch.WordTrace]
  refine ⟨35084250567117368962474099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46779000756156491949965465 35084250567117368962474099)
  ·
    refine ⟨52626375850676053443711149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35084250567117368962474099 52626375850676053443711149)
    ·
      refine ⟨19734890944003520041391681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52626375850676053443711149 19734890944003520041391681)
      ·
        refine ⟨14801168208002640031043761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19734890944003520041391681 14801168208002640031043761)
        ·
          refine ⟨11100876156001980023282821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14801168208002640031043761 11100876156001980023282821)
          ·
            refine ⟨2081414279250371254365529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11100876156001980023282821 2081414279250371254365529)
            ·
              refine ⟨1561060709437778440774147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2081414279250371254365529 1561060709437778440774147)
              ·
                refine ⟨2341591064156667661161221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1561060709437778440774147 2341591064156667661161221)
                ·
                  refine ⟨439048324529375186467729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2341591064156667661161221 439048324529375186467729)
                  ·
                    rfl

theorem cell21_1923848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 4].length) (baseStart_1923848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1923848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1923848 prefixEnd_1923848 := by exact prefixLift 1923848
  have htrace : WordTrace (prefixWord ++ tailWord_1923848) baseStart_1923848 baseEnd_1923848 := by
    simpa [prefixWord, tailWord_1923848, baseEnd_1923848] using wordTrace_append hprefix tailTrace_1923848
  have hstable : (prefixWord ++ tailWord_1923848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923848).length < 2 ^ (prefixWord ++ tailWord_1923848).sum := by decide
  have hdescent : baseEnd_1923848 < baseStart_1923848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923885 : List Nat := [1, 5, 3, 2, 2, 1, 2, 2, 3]
def baseStart_1923885 : Nat := 118140960795 + 1923885 * 2 ^ 59
def prefixEnd_1923885 : Nat := 4983230072969 + 3 ^ 40 * 1923885 * 2
def baseEnd_1923885 : Nat := 439056768433471344350987

theorem tailTrace_1923885 : CollatzResearch.WordTrace tailWord_1923885 prefixEnd_1923885 439056768433471344350987 := by
  unfold tailWord_1923885
  simp only [CollatzResearch.WordTrace]
  refine ⟨70169850635100693244045109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46779900423400462162696739 70169850635100693244045109)
  ·
    refine ⟨6578423497040689991629229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70169850635100693244045109 6578423497040689991629229)
    ·
      refine ⟨2466908811390258746860961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6578423497040689991629229 2466908811390258746860961)
      ·
        refine ⟨1850181608542694060145721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2466908811390258746860961 1850181608542694060145721)
        ·
          refine ⟨1387636206407020545109291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1850181608542694060145721 1387636206407020545109291)
          ·
            refine ⟨2081454309610530817663937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1387636206407020545109291 2081454309610530817663937)
            ·
              refine ⟨1561090732207898113247953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2081454309610530817663937 1561090732207898113247953)
              ·
                refine ⟨1170818049155923584935965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1561090732207898113247953 1170818049155923584935965)
                ·
                  refine ⟨439056768433471344350987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1170818049155923584935965 439056768433471344350987)
                  ·
                    rfl

theorem cell21_1923885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_1923885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1923885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1923885 prefixEnd_1923885 := by exact prefixLift 1923885
  have htrace : WordTrace (prefixWord ++ tailWord_1923885) baseStart_1923885 baseEnd_1923885 := by
    simpa [prefixWord, tailWord_1923885, baseEnd_1923885] using wordTrace_append hprefix tailTrace_1923885
  have hstable : (prefixWord ++ tailWord_1923885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923885).length < 2 ^ (prefixWord ++ tailWord_1923885).sum := by decide
  have hdescent : baseEnd_1923885 < baseStart_1923885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923893 : List Nat := [1, 3, 3, 1, 3, 2, 1, 4, 3]
def baseStart_1923893 : Nat := 118140960795 + 1923893 * 2 ^ 59
def prefixEnd_1923893 : Nat := 4983230072969 + 3 ^ 40 * 1923893 * 2
def baseEnd_1923893 : Nat := 439058594142465108217637

theorem tailTrace_1923893 : CollatzResearch.WordTrace tailWord_1923893 prefixEnd_1923893 439058594142465108217637 := by
  unfold tailWord_1923893
  simp only [CollatzResearch.WordTrace]
  refine ⟨70170142419071710610336333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46780094946047807073557555 70170142419071710610336333)
  ·
    refine ⟨26313803407151891478876125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70170142419071710610336333 26313803407151891478876125)
    ·
      refine ⟨9867676277681959304578547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26313803407151891478876125 9867676277681959304578547)
      ·
        refine ⟨14801514416522938956867821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9867676277681959304578547 14801514416522938956867821)
        ·
          refine ⟨5550567906196102108825433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14801514416522938956867821 5550567906196102108825433)
          ·
            refine ⟨4162925929647076581619075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5550567906196102108825433 4162925929647076581619075)
            ·
              refine ⟨6244388894470614872428613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4162925929647076581619075 6244388894470614872428613)
              ·
                refine ⟨1170822917713240288580365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6244388894470614872428613 1170822917713240288580365)
                ·
                  refine ⟨439058594142465108217637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1170822917713240288580365 439058594142465108217637)
                  ·
                    rfl

theorem cell21_1923893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4, 3].length) (baseStart_1923893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1923893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1923893 prefixEnd_1923893 := by exact prefixLift 1923893
  have htrace : WordTrace (prefixWord ++ tailWord_1923893) baseStart_1923893 baseEnd_1923893 := by
    simpa [prefixWord, tailWord_1923893, baseEnd_1923893] using wordTrace_append hprefix tailTrace_1923893
  have hstable : (prefixWord ++ tailWord_1923893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923893).length < 2 ^ (prefixWord ++ tailWord_1923893).sum := by decide
  have hdescent : baseEnd_1923893 < baseStart_1923893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923910 : List Nat := [6, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_1923910 : Nat := 118140960795 + 1923910 * 2 ^ 59
def prefixEnd_1923910 : Nat := 4983230072969 + 3 ^ 40 * 1923910 * 2
def baseEnd_1923910 : Nat := 439062473774076856434269

theorem tailTrace_1923910 : CollatzResearch.WordTrace tailWord_1923910 prefixEnd_1923910 439062473774076856434269 := by
  unfold tailWord_1923910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2192836326875316328553287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46780508306673415009136789 2192836326875316328553287)
  ·
    refine ⟨3289254490312974492829931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2192836326875316328553287 3289254490312974492829931)
    ·
      refine ⟨4933881735469461739244897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3289254490312974492829931 4933881735469461739244897)
      ·
        refine ⟨3700411301602096304433673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4933881735469461739244897 3700411301602096304433673)
        ·
          refine ⟨2775308476201572228325255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3700411301602096304433673 2775308476201572228325255)
          ·
            refine ⟨4162962714302358342487883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2775308476201572228325255 4162962714302358342487883)
            ·
              refine ⟨6244444071453537513731825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4162962714302358342487883 6244444071453537513731825)
              ·
                refine ⟨4683333053590153135298869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6244444071453537513731825 4683333053590153135298869)
                ·
                  refine ⟨439062473774076856434269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4683333053590153135298869 439062473774076856434269)
                  ·
                    rfl

theorem cell21_1923910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_1923910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1923910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1923910 prefixEnd_1923910 := by exact prefixLift 1923910
  have htrace : WordTrace (prefixWord ++ tailWord_1923910) baseStart_1923910 baseEnd_1923910 := by
    simpa [prefixWord, tailWord_1923910, baseEnd_1923910] using wordTrace_append hprefix tailTrace_1923910
  have hstable : (prefixWord ++ tailWord_1923910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923910).length < 2 ^ (prefixWord ++ tailWord_1923910).sum := by decide
  have hdescent : baseEnd_1923910 < baseStart_1923910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1923952 : List Nat := [2, 1, 1, 1, 4, 1, 4, 4, 3]
def baseStart_1923952 : Nat := 118140960795 + 1923952 * 2 ^ 59
def prefixEnd_1923952 : Nat := 4983230072969 + 3 ^ 40 * 1923952 * 2
def baseEnd_1923952 : Nat := 439072058746294116734183

theorem tailTrace_1923952 : CollatzResearch.WordTrace tailWord_1923952 prefixEnd_1923952 439072058746294116734183 := by
  unfold tailWord_1923952
  simp only [CollatzResearch.WordTrace]
  refine ⟨35086147162928981843367055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46781529550571975791156073 35086147162928981843367055)
  ·
    refine ⟨52629220744393472765050583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35086147162928981843367055 52629220744393472765050583)
    ·
      refine ⟨78943831116590209147575875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52629220744393472765050583 78943831116590209147575875)
      ·
        refine ⟨118415746674885313721363813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78943831116590209147575875 118415746674885313721363813)
        ·
          refine ⟨22202952501540996322755715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118415746674885313721363813 22202952501540996322755715)
          ·
            refine ⟨33304428752311494484133573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22202952501540996322755715 33304428752311494484133573)
            ·
              refine ⟨6244580391058405215775045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33304428752311494484133573 6244580391058405215775045)
              ·
                refine ⟨1170858823323450977957821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6244580391058405215775045 1170858823323450977957821)
                ·
                  refine ⟨439072058746294116734183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1170858823323450977957821 439072058746294116734183)
                  ·
                    rfl

theorem cell21_1923952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4, 3].length) (baseStart_1923952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1923952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1923952 prefixEnd_1923952 := by exact prefixLift 1923952
  have htrace : WordTrace (prefixWord ++ tailWord_1923952) baseStart_1923952 baseEnd_1923952 := by
    simpa [prefixWord, tailWord_1923952, baseEnd_1923952] using wordTrace_append hprefix tailTrace_1923952
  have hstable : (prefixWord ++ tailWord_1923952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1923952).length < 2 ^ (prefixWord ++ tailWord_1923952).sum := by decide
  have hdescent : baseEnd_1923952 < baseStart_1923952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1923952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924017 : List Nat := [1, 2, 2, 4, 4, 1, 2, 1, 4]
def baseStart_1924017 : Nat := 118140960795 + 1924017 * 2 ^ 59
def prefixEnd_1924017 : Nat := 4983230072969 + 3 ^ 40 * 1924017 * 2
def baseEnd_1924017 : Nat := 439086892631868448150717

theorem tailTrace_1924017 : CollatzResearch.WordTrace tailWord_1924017 prefixEnd_1924017 439086892631868448150717 := by
  unfold tailWord_1924017
  simp only [CollatzResearch.WordTrace]
  refine ⟨70174665070622479787850305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46783110047081653191900203 70174665070622479787850305)
  ·
    refine ⟨52630998802966859840887729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70174665070622479787850305 52630998802966859840887729)
    ·
      refine ⟨39473249102225144880665797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52630998802966859840887729 39473249102225144880665797)
      ·
        refine ⟨7401234206667214665124837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39473249102225144880665797 7401234206667214665124837)
        ·
          refine ⟨1387731413750102749710907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7401234206667214665124837 1387731413750102749710907)
          ·
            refine ⟨2081597120625154124566361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1387731413750102749710907 2081597120625154124566361)
            ·
              refine ⟨1561197840468865593424771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2081597120625154124566361 1561197840468865593424771)
              ·
                refine ⟨2341796760703298390137157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1561197840468865593424771 2341796760703298390137157)
                ·
                  refine ⟨439086892631868448150717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2341796760703298390137157 439086892631868448150717)
                  ·
                    rfl

theorem cell21_1924017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 4].length) (baseStart_1924017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1924017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1924017 prefixEnd_1924017 := by exact prefixLift 1924017
  have htrace : WordTrace (prefixWord ++ tailWord_1924017) baseStart_1924017 baseEnd_1924017 := by
    simpa [prefixWord, tailWord_1924017, baseEnd_1924017] using wordTrace_append hprefix tailTrace_1924017
  have hstable : (prefixWord ++ tailWord_1924017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924017).length < 2 ^ (prefixWord ++ tailWord_1924017).sum := by decide
  have hdescent : baseEnd_1924017 < baseStart_1924017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924101 : List Nat := [1, 3, 1, 1, 2, 3, 2, 2, 6]
def baseStart_1924101 : Nat := 118140960795 + 1924101 * 2 ^ 59
def prefixEnd_1924101 : Nat := 4983230072969 + 3 ^ 40 * 1924101 * 2
def baseEnd_1924101 : Nat := 439106062576302968750545

theorem tailTrace_1924101 : CollatzResearch.WordTrace tailWord_1924101 prefixEnd_1924101 439106062576302968750545 := by
  unfold tailWord_1924101
  simp only [CollatzResearch.WordTrace]
  refine ⟨70177728802318162133908157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46785152534878774755938771 70177728802318162133908157)
  ·
    refine ⟨26316648300869310800215559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70177728802318162133908157 26316648300869310800215559)
    ·
      refine ⟨39474972451303966200323339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26316648300869310800215559 39474972451303966200323339)
      ·
        refine ⟨59212458676955949300485009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39474972451303966200323339 59212458676955949300485009)
        ·
          refine ⟨44409344007716961975363757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59212458676955949300485009 44409344007716961975363757)
          ·
            refine ⟨16653504002893860740761409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44409344007716961975363757 16653504002893860740761409)
            ·
              refine ⟨12490128002170395555571057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16653504002893860740761409 12490128002170395555571057)
              ·
                refine ⟨9367596001627796666678293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12490128002170395555571057 9367596001627796666678293)
                ·
                  refine ⟨439106062576302968750545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9367596001627796666678293 439106062576302968750545)
                  ·
                    rfl

theorem cell21_1924101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_1924101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1924101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1924101 prefixEnd_1924101 := by exact prefixLift 1924101
  have htrace : WordTrace (prefixWord ++ tailWord_1924101) baseStart_1924101 baseEnd_1924101 := by
    simpa [prefixWord, tailWord_1924101, baseEnd_1924101] using wordTrace_append hprefix tailTrace_1924101
  have hstable : (prefixWord ++ tailWord_1924101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924101).length < 2 ^ (prefixWord ++ tailWord_1924101).sum := by decide
  have hdescent : baseEnd_1924101 < baseStart_1924101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924104 : List Nat := [2, 1, 3, 2, 1, 3, 1, 5, 3]
def baseStart_1924104 : Nat := 118140960795 + 1924104 * 2 ^ 59
def prefixEnd_1924104 : Nat := 4983230072969 + 3 ^ 40 * 1924104 * 2
def baseEnd_1924104 : Nat := 439106747217175630200539

theorem tailTrace_1924104 : CollatzResearch.WordTrace tailWord_1924104 prefixEnd_1924104 439106747217175630200539 := by
  unfold tailWord_1924104
  simp only [CollatzResearch.WordTrace]
  refine ⟨35088919110653646823133683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46785225480871529097511577 35088919110653646823133683)
  ·
    refine ⟨52633378665980470234700525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35088919110653646823133683 52633378665980470234700525)
    ·
      refine ⟨19737516999742676338012697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52633378665980470234700525 19737516999742676338012697)
      ·
        refine ⟨14803137749807007253509523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19737516999742676338012697 14803137749807007253509523)
        ·
          refine ⟨22204706624710510880264285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14803137749807007253509523 22204706624710510880264285)
          ·
            refine ⟨8326764984266441580099107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22204706624710510880264285 8326764984266441580099107)
            ·
              refine ⟨12490147476399662370148661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8326764984266441580099107 12490147476399662370148661)
              ·
                refine ⟨1170951325912468347201437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12490147476399662370148661 1170951325912468347201437)
                ·
                  refine ⟨439106747217175630200539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1170951325912468347201437 439106747217175630200539)
                  ·
                    rfl

theorem cell21_1924104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5, 3].length) (baseStart_1924104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1924104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1924104 prefixEnd_1924104 := by exact prefixLift 1924104
  have htrace : WordTrace (prefixWord ++ tailWord_1924104) baseStart_1924104 baseEnd_1924104 := by
    simpa [prefixWord, tailWord_1924104, baseEnd_1924104] using wordTrace_append hprefix tailTrace_1924104
  have hstable : (prefixWord ++ tailWord_1924104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924104).length < 2 ^ (prefixWord ++ tailWord_1924104).sum := by decide
  have hdescent : baseEnd_1924104 < baseStart_1924104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924166 : List Nat := [6, 1, 1, 1, 1, 4, 7]
def baseStart_1924166 : Nat := 118140960795 + 1924166 * 2 ^ 59
def prefixEnd_1924166 : Nat := 4983230072969 + 3 ^ 40 * 1924166 * 2
def baseEnd_1924166 : Nat := 48791210717986366685231

theorem tailTrace_1924166 : CollatzResearch.WordTrace tailWord_1924166 prefixEnd_1924166 48791210717986366685231 := by
  unfold tailWord_1924166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2193128110846333694844511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46786733031388452156682901 2193128110846333694844511)
  ·
    refine ⟨3289692166269500542266767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2193128110846333694844511 3289692166269500542266767)
    ·
      refine ⟨4934538249404250813400151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3289692166269500542266767 4934538249404250813400151)
      ·
        refine ⟨7401807374106376220100227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4934538249404250813400151 7401807374106376220100227)
        ·
          refine ⟨11102711061159564330150341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7401807374106376220100227 11102711061159564330150341)
          ·
            refine ⟨2081758323967418311903189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11102711061159564330150341 2081758323967418311903189)
            ·
              refine ⟨48791210717986366685231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2081758323967418311903189 48791210717986366685231)
              ·
                rfl

theorem cell21_1924166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 7].length) (baseStart_1924166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1924166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1924166 prefixEnd_1924166 := by exact prefixLift 1924166
  have htrace : WordTrace (prefixWord ++ tailWord_1924166) baseStart_1924166 baseEnd_1924166 := by
    simpa [prefixWord, tailWord_1924166, baseEnd_1924166] using wordTrace_append hprefix tailTrace_1924166
  have hstable : (prefixWord ++ tailWord_1924166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924166).length < 2 ^ (prefixWord ++ tailWord_1924166).sum := by decide
  have hdescent : baseEnd_1924166 < baseStart_1924166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924177 : List Nat := [1, 2, 2, 1, 3, 1, 4, 1, 6]
def baseStart_1924177 : Nat := 118140960795 + 1924177 * 2 ^ 59
def prefixEnd_1924177 : Nat := 4983230072969 + 3 ^ 40 * 1924177 * 2
def baseEnd_1924177 : Nat := 439123406811743725483723

theorem tailTrace_1924177 : CollatzResearch.WordTrace tailWord_1924177 prefixEnd_1924177 439123406811743725483723 := by
  unfold tailWord_1924177
  simp only [CollatzResearch.WordTrace]
  refine ⟨70180500750042827113674785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46787000500028551409116523 70180500750042827113674785)
  ·
    refine ⟨52635375562532120335256089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70180500750042827113674785 52635375562532120335256089)
    ·
      refine ⟨39476531671899090251442067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52635375562532120335256089 39476531671899090251442067)
      ·
        refine ⟨59214797507848635377163101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39476531671899090251442067 59214797507848635377163101)
        ·
          refine ⟨22205549065443238266436163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59214797507848635377163101 22205549065443238266436163)
          ·
            refine ⟨33308323598164857399654245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22205549065443238266436163 33308323598164857399654245)
            ·
              refine ⟨6245310674655910762435171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33308323598164857399654245 6245310674655910762435171)
              ·
                refine ⟨9367966011983866143652757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6245310674655910762435171 9367966011983866143652757)
                ·
                  refine ⟨439123406811743725483723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9367966011983866143652757 439123406811743725483723)
                  ·
                    rfl

theorem cell21_1924177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 6].length) (baseStart_1924177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1924177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1924177 prefixEnd_1924177 := by exact prefixLift 1924177
  have htrace : WordTrace (prefixWord ++ tailWord_1924177) baseStart_1924177 baseEnd_1924177 := by
    simpa [prefixWord, tailWord_1924177, baseEnd_1924177] using wordTrace_append hprefix tailTrace_1924177
  have hstable : (prefixWord ++ tailWord_1924177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924177).length < 2 ^ (prefixWord ++ tailWord_1924177).sum := by decide
  have hdescent : baseEnd_1924177 < baseStart_1924177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924180 : List Nat := [2, 4, 1, 1, 1, 1, 2, 6, 3]
def baseStart_1924180 : Nat := 118140960795 + 1924180 * 2 ^ 59
def prefixEnd_1924180 : Nat := 4983230072969 + 3 ^ 40 * 1924180 * 2
def baseEnd_1924180 : Nat := 439124091452616386933717

theorem tailTrace_1924180 : CollatzResearch.WordTrace tailWord_1924180 prefixEnd_1924180 439124091452616386933717 := by
  unfold tailWord_1924180
  simp only [CollatzResearch.WordTrace]
  refine ⟨35090305084515979313016997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46787073446021305750689329 35090305084515979313016997)
  ·
    refine ⟨6579432203346746121190687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35090305084515979313016997 6579432203346746121190687)
    ·
      refine ⟨9869148305020119181786031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6579432203346746121190687 9869148305020119181786031)
      ·
        refine ⟨14803722457530178772679047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9869148305020119181786031 14803722457530178772679047)
        ·
          refine ⟨22205583686295268159018571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14803722457530178772679047 22205583686295268159018571)
          ·
            refine ⟨33308375529442902238527857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22205583686295268159018571 33308375529442902238527857)
            ·
              refine ⟨24981281647082176678895893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33308375529442902238527857 24981281647082176678895893)
              ·
                refine ⟨1170997577206977031823245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24981281647082176678895893 1170997577206977031823245)
                ·
                  refine ⟨439124091452616386933717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1170997577206977031823245 439124091452616386933717)
                  ·
                    rfl

theorem cell21_1924180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_1924180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1924180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1924180 prefixEnd_1924180 := by exact prefixLift 1924180
  have htrace : WordTrace (prefixWord ++ tailWord_1924180) baseStart_1924180 baseEnd_1924180 := by
    simpa [prefixWord, tailWord_1924180, baseEnd_1924180] using wordTrace_append hprefix tailTrace_1924180
  have hstable : (prefixWord ++ tailWord_1924180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924180).length < 2 ^ (prefixWord ++ tailWord_1924180).sum := by decide
  have hdescent : baseEnd_1924180 < baseStart_1924180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924273 : List Nat := [1, 2, 2, 5, 1, 2, 2, 3, 3]
def baseStart_1924273 : Nat := 118140960795 + 1924273 * 2 ^ 59
def prefixEnd_1924273 : Nat := 4983230072969 + 3 ^ 40 * 1924273 * 2
def baseEnd_1924273 : Nat := 439145315319668891883527

theorem tailTrace_1924273 : CollatzResearch.WordTrace tailWord_1924273 prefixEnd_1924273 439145315319668891883527 := by
  unfold tailWord_1924273
  simp only [CollatzResearch.WordTrace]
  refine ⟨70184002157695035509169473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46789334771796690339446315 70184002157695035509169473)
  ·
    refine ⟨52638001618271276631877105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70184002157695035509169473 52638001618271276631877105)
    ·
      refine ⟨39478501213703457473907829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52638001618271276631877105 39478501213703457473907829)
      ·
        refine ⟨3701109488784699138178859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39478501213703457473907829 3701109488784699138178859)
        ·
          refine ⟨5551664233177048707268289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3701109488784699138178859 5551664233177048707268289)
          ·
            refine ⟨4163748174882786530451217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5551664233177048707268289 4163748174882786530451217)
            ·
              refine ⟨3122811131162089897838413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4163748174882786530451217 3122811131162089897838413)
              ·
                refine ⟨1171054174185783711689405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3122811131162089897838413 1171054174185783711689405)
                ·
                  refine ⟨439145315319668891883527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1171054174185783711689405 439145315319668891883527)
                  ·
                    rfl

theorem cell21_1924273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3, 3].length) (baseStart_1924273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1924273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1924273 prefixEnd_1924273 := by exact prefixLift 1924273
  have htrace : WordTrace (prefixWord ++ tailWord_1924273) baseStart_1924273 baseEnd_1924273 := by
    simpa [prefixWord, tailWord_1924273, baseEnd_1924273] using wordTrace_append hprefix tailTrace_1924273
  have hstable : (prefixWord ++ tailWord_1924273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924273).length < 2 ^ (prefixWord ++ tailWord_1924273).sum := by decide
  have hdescent : baseEnd_1924273 < baseStart_1924273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924284 : List Nat := [2, 2, 2, 3, 2, 2, 8]
def baseStart_1924284 : Nat := 118140960795 + 1924284 * 2 ^ 59
def prefixEnd_1924284 : Nat := 4983230072969 + 3 ^ 40 * 1924284 * 2
def baseEnd_1924284 : Nat := 48794202852170590800019

theorem tailTrace_1924284 : CollatzResearch.WordTrace tailWord_1924284 prefixEnd_1924284 48794202852170590800019 := by
  unfold tailWord_1924284
  simp only [CollatzResearch.WordTrace]
  refine ⟨35092201680327592193909953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46789602240436789591879937 35092201680327592193909953)
  ·
    refine ⟨26319151260245694145432465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35092201680327592193909953 26319151260245694145432465)
    ·
      refine ⟨19739363445184270609074349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26319151260245694145432465 19739363445184270609074349)
      ·
        refine ⟨7402261291944101478402881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19739363445184270609074349 7402261291944101478402881)
        ·
          refine ⟨5551695968958076108802161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7402261291944101478402881 5551695968958076108802161)
          ·
            refine ⟨4163771976718557081601621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5551695968958076108802161 4163771976718557081601621)
            ·
              refine ⟨48794202852170590800019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4163771976718557081601621 48794202852170590800019)
              ·
                rfl

theorem cell21_1924284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 8].length) (baseStart_1924284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1924284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1924284 prefixEnd_1924284 := by exact prefixLift 1924284
  have htrace : WordTrace (prefixWord ++ tailWord_1924284) baseStart_1924284 baseEnd_1924284 := by
    simpa [prefixWord, tailWord_1924284, baseEnd_1924284] using wordTrace_append hprefix tailTrace_1924284
  have hstable : (prefixWord ++ tailWord_1924284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924284).length < 2 ^ (prefixWord ++ tailWord_1924284).sum := by decide
  have hdescent : baseEnd_1924284 < baseStart_1924284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924290 : List Nat := [3, 5, 1, 1, 2, 1, 2, 1, 5]
def baseStart_1924290 : Nat := 118140960795 + 1924290 * 2 ^ 59
def prefixEnd_1924290 : Nat := 4983230072969 + 3 ^ 40 * 1924290 * 2
def baseEnd_1924290 : Nat := 439149194951280640100159

theorem tailTrace_1924290 : CollatzResearch.WordTrace tailWord_1924290 prefixEnd_1924290 439149194951280640100159 := by
  unfold tailWord_1924290
  simp only [CollatzResearch.WordTrace]
  refine ⟨17546155549658361853134581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46789748132422298275025549 17546155549658361853134581)
  ·
    refine ⟨1644952082780471423731367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17546155549658361853134581 1644952082780471423731367)
    ·
      refine ⟨2467428124170707135597051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1644952082780471423731367 2467428124170707135597051)
      ·
        refine ⟨3701142186256060703395577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2467428124170707135597051 3701142186256060703395577)
        ·
          refine ⟨2775856639692045527546683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3701142186256060703395577 2775856639692045527546683)
          ·
            refine ⟨4163784959538068291320025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2775856639692045527546683 4163784959538068291320025)
            ·
              refine ⟨3122838719653551218490019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4163784959538068291320025 3122838719653551218490019)
              ·
                refine ⟨4684258079480326827735029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3122838719653551218490019 4684258079480326827735029)
                ·
                  refine ⟨439149194951280640100159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4684258079480326827735029 439149194951280640100159)
                  ·
                    rfl

theorem cell21_1924290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_1924290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1924290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1924290 prefixEnd_1924290 := by exact prefixLift 1924290
  have htrace : WordTrace (prefixWord ++ tailWord_1924290) baseStart_1924290 baseEnd_1924290 := by
    simpa [prefixWord, tailWord_1924290, baseEnd_1924290] using wordTrace_append hprefix tailTrace_1924290
  have hstable : (prefixWord ++ tailWord_1924290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924290).length < 2 ^ (prefixWord ++ tailWord_1924290).sum := by decide
  have hdescent : baseEnd_1924290 < baseStart_1924290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924332 : List Nat := [2, 2, 1, 1, 2, 4, 3, 3, 3]
def baseStart_1924332 : Nat := 118140960795 + 1924332 * 2 ^ 59
def prefixEnd_1924332 : Nat := 4983230072969 + 3 ^ 40 * 1924332 * 2
def baseEnd_1924332 : Nat := 439158779923497900400073

theorem tailTrace_1924332 : CollatzResearch.WordTrace tailWord_1924332 prefixEnd_1924332 439158779923497900400073 := by
  unfold tailWord_1924332
  simp only [CollatzResearch.WordTrace]
  refine ⟨35093077032240644292783625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46790769376320859057044833 35093077032240644292783625)
  ·
    refine ⟨26319807774180483219587719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35093077032240644292783625 26319807774180483219587719)
    ·
      refine ⟨39479711661270724829381579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26319807774180483219587719 39479711661270724829381579)
      ·
        refine ⟨59219567491906087244072369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39479711661270724829381579 59219567491906087244072369)
        ·
          refine ⟨44414675618929565433054277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59219567491906087244072369 44414675618929565433054277)
          ·
            refine ⟨8327751678549293518697677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44414675618929565433054277 8327751678549293518697677)
            ·
              refine ⟨3122906879455985069511629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8327751678549293518697677 3122906879455985069511629)
              ·
                refine ⟨1171090079795994401066861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3122906879455985069511629 1171090079795994401066861)
                ·
                  refine ⟨439158779923497900400073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1171090079795994401066861 439158779923497900400073)
                  ·
                    rfl

theorem cell21_1924332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3, 3].length) (baseStart_1924332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1924332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1924332 prefixEnd_1924332 := by exact prefixLift 1924332
  have htrace : WordTrace (prefixWord ++ tailWord_1924332) baseStart_1924332 baseEnd_1924332 := by
    simpa [prefixWord, tailWord_1924332, baseEnd_1924332] using wordTrace_append hprefix tailTrace_1924332
  have hstable : (prefixWord ++ tailWord_1924332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924332).length < 2 ^ (prefixWord ++ tailWord_1924332).sum := by decide
  have hdescent : baseEnd_1924332 < baseStart_1924332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924363 : List Nat := [1, 1, 1, 1, 5, 5, 2, 1, 4]
def baseStart_1924363 : Nat := 118140960795 + 1924363 * 2 ^ 59
def prefixEnd_1924363 : Nat := 4983230072969 + 3 ^ 40 * 1924363 * 2
def baseEnd_1924363 : Nat := 439165854545848735383343

theorem tailTrace_1924363 : CollatzResearch.WordTrace tailWord_1924363 prefixEnd_1924363 439165854545848735383343 := by
  unfold tailWord_1924363
  simp only [CollatzResearch.WordTrace]
  refine ⟨70187284727368980879945743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46791523151579320586630495 70187284727368980879945743)
  ·
    refine ⟨105280927091053471319918615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70187284727368980879945743 105280927091053471319918615)
    ·
      refine ⟨157921390636580206979877923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105280927091053471319918615 157921390636580206979877923)
      ·
        refine ⟨236882085954870310469816885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157921390636580206979877923 236882085954870310469816885)
        ·
          refine ⟨22207695558269091606545333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 236882085954870310469816885 22207695558269091606545333)
          ·
            refine ⟨2081971458587727338113625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22207695558269091606545333 2081971458587727338113625)
            ·
              refine ⟨1561478593940795503585219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2081971458587727338113625 1561478593940795503585219)
              ·
                refine ⟨2342217890911193255377829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1561478593940795503585219 2342217890911193255377829)
                ·
                  refine ⟨439165854545848735383343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2342217890911193255377829 439165854545848735383343)
                  ·
                    rfl

theorem cell21_1924363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 4].length) (baseStart_1924363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1924363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1924363 prefixEnd_1924363 := by exact prefixLift 1924363
  have htrace : WordTrace (prefixWord ++ tailWord_1924363) baseStart_1924363 baseEnd_1924363 := by
    simpa [prefixWord, tailWord_1924363, baseEnd_1924363] using wordTrace_append hprefix tailTrace_1924363
  have hstable : (prefixWord ++ tailWord_1924363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924363).length < 2 ^ (prefixWord ++ tailWord_1924363).sum := by decide
  have hdescent : baseEnd_1924363 < baseStart_1924363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924456 : List Nat := [2, 1, 4, 2, 4, 1, 1, 2, 4]
def baseStart_1924456 : Nat := 118140960795 + 1924456 * 2 ^ 59
def prefixEnd_1924456 : Nat := 4983230072969 + 3 ^ 40 * 1924456 * 2
def baseEnd_1924456 : Nat := 439187078412901240333153

theorem tailTrace_1924456 : CollatzResearch.WordTrace tailWord_1924456 prefixEnd_1924456 439187078412901240333153 := by
  unfold tailWord_1924456
  simp only [CollatzResearch.WordTrace]
  refine ⟨35095338358016028881540611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46793784477354705175387481 35095338358016028881540611)
  ·
    refine ⟨52643007537024043322310917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35095338358016028881540611 52643007537024043322310917)
    ·
      refine ⟨9870563913192008122933297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52643007537024043322310917 9870563913192008122933297)
      ·
        refine ⟨7402922934894006092199973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9870563913192008122933297 7402922934894006092199973)
        ·
          refine ⟨1388048050292626142287495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7402922934894006092199973 1388048050292626142287495)
          ·
            refine ⟨2082072075438939213431243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1388048050292626142287495 2082072075438939213431243)
            ·
              refine ⟨3123108113158408820146865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2082072075438939213431243 3123108113158408820146865)
              ·
                refine ⟨2342331084868806615110149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3123108113158408820146865 2342331084868806615110149)
                ·
                  refine ⟨439187078412901240333153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2342331084868806615110149 439187078412901240333153)
                  ·
                    rfl

theorem cell21_1924456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 4].length) (baseStart_1924456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1924456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1924456 prefixEnd_1924456 := by exact prefixLift 1924456
  have htrace : WordTrace (prefixWord ++ tailWord_1924456) baseStart_1924456 baseEnd_1924456 := by
    simpa [prefixWord, tailWord_1924456, baseEnd_1924456] using wordTrace_append hprefix tailTrace_1924456
  have hstable : (prefixWord ++ tailWord_1924456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924456).length < 2 ^ (prefixWord ++ tailWord_1924456).sum := by decide
  have hdescent : baseEnd_1924456 < baseStart_1924456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924577 : List Nat := [1, 2, 3, 1, 2, 5, 2, 2, 3]
def baseStart_1924577 : Nat := 118140960795 + 1924577 * 2 ^ 59
def prefixEnd_1924577 : Nat := 4983230072969 + 3 ^ 40 * 1924577 * 2
def baseEnd_1924577 : Nat := 439214692261431918816239

theorem tailTrace_1924577 : CollatzResearch.WordTrace tailWord_1924577 prefixEnd_1924577 439214692261431918816239 := by
  unfold tailWord_1924577
  simp only [CollatzResearch.WordTrace]
  refine ⟨70195089948593695428235985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46796726632395796952157323 70195089948593695428235985)
  ·
    refine ⟨52646317461445271571176989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70195089948593695428235985 52646317461445271571176989)
    ·
      refine ⟨19742369048041976839191371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52646317461445271571176989 19742369048041976839191371)
      ·
        refine ⟨29613553572062965258787057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19742369048041976839191371 29613553572062965258787057)
        ·
          refine ⟨22210165179047223944090293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29613553572062965258787057 22210165179047223944090293)
          ·
            refine ⟨2082202985535677244758465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22210165179047223944090293 2082202985535677244758465)
            ·
              refine ⟨1561652239151757933568849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2082202985535677244758465 1561652239151757933568849)
              ·
                refine ⟨1171239179363818450176637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1561652239151757933568849 1171239179363818450176637)
                ·
                  refine ⟨439214692261431918816239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1171239179363818450176637 439214692261431918816239)
                  ·
                    rfl

theorem cell21_1924577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2, 3].length) (baseStart_1924577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1924577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1924577 prefixEnd_1924577 := by exact prefixLift 1924577
  have htrace : WordTrace (prefixWord ++ tailWord_1924577) baseStart_1924577 baseEnd_1924577 := by
    simpa [prefixWord, tailWord_1924577, baseEnd_1924577] using wordTrace_append hprefix tailTrace_1924577
  have hstable : (prefixWord ++ tailWord_1924577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924577).length < 2 ^ (prefixWord ++ tailWord_1924577).sum := by decide
  have hdescent : baseEnd_1924577 < baseStart_1924577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924602 : List Nat := [3, 1, 1, 1, 1, 2, 5, 2, 5]
def baseStart_1924602 : Nat := 118140960795 + 1924602 * 2 ^ 59
def prefixEnd_1924602 : Nat := 4983230072969 + 3 ^ 40 * 1924602 * 2
def baseEnd_1924602 : Nat := 439220397602037430899521

theorem tailTrace_1924602 : CollatzResearch.WordTrace tailWord_1924602 prefixEnd_1924602 439220397602037430899521 := by
  unfold tailWord_1924602
  simp only [CollatzResearch.WordTrace]
  refine ⟨17549000443375781174474015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46797334515668749798597373 17549000443375781174474015)
  ·
    refine ⟨26323500665063671761711023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17549000443375781174474015 26323500665063671761711023)
    ·
      refine ⟨39485250997595507642566535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26323500665063671761711023 39485250997595507642566535)
      ·
        refine ⟨59227876496393261463849803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39485250997595507642566535 59227876496393261463849803)
        ·
          refine ⟨88841814744589892195774705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59227876496393261463849803 88841814744589892195774705)
          ·
            refine ⟨66631361058442419146831029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88841814744589892195774705 66631361058442419146831029)
            ·
              refine ⟨6246690099228976795015409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66631361058442419146831029 6246690099228976795015409)
              ·
                refine ⟨4685017574421732596261557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6246690099228976795015409 4685017574421732596261557)
                ·
                  refine ⟨439220397602037430899521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4685017574421732596261557 439220397602037430899521)
                  ·
                    rfl

theorem cell21_1924602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_1924602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1924602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1924602 prefixEnd_1924602 := by exact prefixLift 1924602
  have htrace : WordTrace (prefixWord ++ tailWord_1924602) baseStart_1924602 baseEnd_1924602 := by
    simpa [prefixWord, tailWord_1924602, baseEnd_1924602] using wordTrace_append hprefix tailTrace_1924602
  have hstable : (prefixWord ++ tailWord_1924602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924602).length < 2 ^ (prefixWord ++ tailWord_1924602).sum := by decide
  have hdescent : baseEnd_1924602 < baseStart_1924602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924664 : List Nat := [2, 1, 2, 1, 4, 2, 4, 5]
def baseStart_1924664 : Nat := 118140960795 + 1924664 * 2 ^ 59
def prefixEnd_1924664 : Nat := 4983230072969 + 3 ^ 40 * 1924664 * 2
def baseEnd_1924664 : Nat := 146411515615579700288687

theorem tailTrace_1924664 : CollatzResearch.WordTrace tailWord_1924664 prefixEnd_1924664 146411515615579700288687 := by
  unfold tailWord_1924664
  simp only [CollatzResearch.WordTrace]
  refine ⟨35099131549639254643326523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46798842066185672857768697 35099131549639254643326523)
  ·
    refine ⟨52648697324458881964989785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35099131549639254643326523 52648697324458881964989785)
    ·
      refine ⟨39486522993344161473742339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52648697324458881964989785 39486522993344161473742339)
      ·
        refine ⟨59229784490016242210613509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39486522993344161473742339 59229784490016242210613509)
        ·
          refine ⟨11105584591878045414490033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59229784490016242210613509 11105584591878045414490033)
          ·
            refine ⟨8329188443908534060867525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11105584591878045414490033 8329188443908534060867525)
            ·
              refine ⟨1561722833232850136412661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8329188443908534060867525 1561722833232850136412661)
              ·
                refine ⟨146411515615579700288687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1561722833232850136412661 146411515615579700288687)
                ·
                  rfl

theorem cell21_1924664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 5].length) (baseStart_1924664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1924664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1924664 prefixEnd_1924664 := by exact prefixLift 1924664
  have htrace : WordTrace (prefixWord ++ tailWord_1924664) baseStart_1924664 baseEnd_1924664 := by
    simpa [prefixWord, tailWord_1924664, baseEnd_1924664] using wordTrace_append hprefix tailTrace_1924664
  have hstable : (prefixWord ++ tailWord_1924664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924664).length < 2 ^ (prefixWord ++ tailWord_1924664).sum := by decide
  have hdescent : baseEnd_1924664 < baseStart_1924664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1924695 : List Nat := [1, 1, 3, 2, 2, 5, 1, 1, 5]
def baseStart_1924695 : Nat := 118140960795 + 1924695 * 2 ^ 59
def prefixEnd_1924695 : Nat := 4983230072969 + 3 ^ 40 * 1924695 * 2
def baseEnd_1924695 : Nat := 439241621469089935849331

theorem tailTrace_1924695 : CollatzResearch.WordTrace tailWord_1924695 prefixEnd_1924695 439241621469089935849331 := by
  unfold tailWord_1924695
  simp only [CollatzResearch.WordTrace]
  refine ⟨70199393762166201581031539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46799595841444134387354359 70199393762166201581031539)
  ·
    refine ⟨105299090643249302371547309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70199393762166201581031539 105299090643249302371547309)
    ·
      refine ⟨39487158991218488389330241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105299090643249302371547309 39487158991218488389330241)
      ·
        refine ⟨29615369243413866291997681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39487158991218488389330241 29615369243413866291997681)
        ·
          refine ⟨22211526932560399718998261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29615369243413866291997681 22211526932560399718998261)
          ·
            refine ⟨2082330649927537473656087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22211526932560399718998261 2082330649927537473656087)
            ·
              refine ⟨3123495974891306210484131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2082330649927537473656087 3123495974891306210484131)
              ·
                refine ⟨4685243962336959315726197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3123495974891306210484131 4685243962336959315726197)
                ·
                  refine ⟨439241621469089935849331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4685243962336959315726197 439241621469089935849331)
                  ·
                    rfl

theorem cell21_1924695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 5].length) (baseStart_1924695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1924695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1924695 prefixEnd_1924695 := by exact prefixLift 1924695
  have htrace : WordTrace (prefixWord ++ tailWord_1924695) baseStart_1924695 baseEnd_1924695 := by
    simpa [prefixWord, tailWord_1924695, baseEnd_1924695] using wordTrace_append hprefix tailTrace_1924695
  have hstable : (prefixWord ++ tailWord_1924695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1924695).length < 2 ^ (prefixWord ++ tailWord_1924695).sum := by decide
  have hdescent : baseEnd_1924695 < baseStart_1924695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1924695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
