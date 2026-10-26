import V185TrunkScan23Chunk0431

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2554248 : List Nat := [2, 1, 3, 3, 1, 1, 1, 3, 8]
def baseStart_2554248 : Nat := 118140960795 + 2554248 * 2 ^ 59
def prefixEnd_2554248 : Nat := 4983230072969 + 3 ^ 40 * 2554248 * 2
def baseEnd_2554248 : Nat := 145728548309491969628137

theorem tailTrace_2554248 : CollatzResearch.WordTrace tailWord_2554248 prefixEnd_2554248 145728548309491969628137 := by
  unfold tailWord_2554248
  simp only [CollatzResearch.WordTrace]
  refine ⟨46580539025201600836699699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62107385366935467782266265 46580539025201600836699699)
  ·
    refine ⟨69870808537802401255049549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46580539025201600836699699 69870808537802401255049549)
    ·
      refine ⟨26201553201675900470643581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69870808537802401255049549 26201553201675900470643581)
      ·
        refine ⟨9825582450628462676491343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26201553201675900470643581 9825582450628462676491343)
        ·
          refine ⟨14738373675942694014737015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9825582450628462676491343 14738373675942694014737015)
          ·
            refine ⟨22107560513914041022105523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14738373675942694014737015 22107560513914041022105523)
            ·
              refine ⟨33161340770871061533158285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22107560513914041022105523 33161340770871061533158285)
              ·
                refine ⟨12435502789076648074934357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33161340770871061533158285 12435502789076648074934357)
                ·
                  refine ⟨145728548309491969628137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12435502789076648074934357 145728548309491969628137)
                  ·
                    rfl

theorem cell23_2554248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 8].length) (baseStart_2554248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554248 prefixEnd_2554248 := by exact prefixLift 2554248
  have htrace : WordTrace (prefixWord ++ tailWord_2554248) baseStart_2554248 baseEnd_2554248 := by
    simpa [prefixWord, tailWord_2554248, baseEnd_2554248] using wordTrace_append hprefix tailTrace_2554248
  have hstable : (prefixWord ++ tailWord_2554248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554248).length < 2 ^ (prefixWord ++ tailWord_2554248).sum := by decide
  have hdescent : baseEnd_2554248 < baseStart_2554248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554252 : List Nat := [2, 2, 1, 2, 1, 6, 1, 1, 3, 4]
def baseStart_2554252 : Nat := 118140960795 + 2554252 * 2 ^ 59
def prefixEnd_2554252 : Nat := 4983230072969 + 3 ^ 40 * 2554252 * 2
def baseEnd_2554252 : Nat := 437186329569348570334405

theorem tailTrace_2554252 : CollatzResearch.WordTrace tailWord_2554252 prefixEnd_2554252 437186329569348570334405 := by
  unfold tailWord_2554252
  simp only [CollatzResearch.WordTrace]
  refine ⟨46580611971194355178272505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62107482628259140237696673 46580611971194355178272505)
  ·
    refine ⟨34935458978395766383704379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46580611971194355178272505 34935458978395766383704379)
    ·
      refine ⟨52403188467593649575556569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34935458978395766383704379 52403188467593649575556569)
      ·
        refine ⟨39302391350695237181667427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52403188467593649575556569 39302391350695237181667427)
        ·
          refine ⟨58953587026042855772501141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39302391350695237181667427 58953587026042855772501141)
          ·
            refine ⟨2763449391845758864335991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58953587026042855772501141 2763449391845758864335991)
            ·
              refine ⟨4145174087768638296503987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2763449391845758864335991 4145174087768638296503987)
              ·
                refine ⟨6217761131652957444755981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4145174087768638296503987 6217761131652957444755981)
                ·
                  refine ⟨2331660424369859041783493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6217761131652957444755981 2331660424369859041783493)
                  ·
                    refine ⟨437186329569348570334405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2331660424369859041783493 437186329569348570334405)
                    ·
                      rfl

theorem cell23_2554252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 3, 4].length) (baseStart_2554252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554252 prefixEnd_2554252 := by exact prefixLift 2554252
  have htrace : WordTrace (prefixWord ++ tailWord_2554252) baseStart_2554252 baseEnd_2554252 := by
    simpa [prefixWord, tailWord_2554252, baseEnd_2554252] using wordTrace_append hprefix tailTrace_2554252
  have hstable : (prefixWord ++ tailWord_2554252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554252).length < 2 ^ (prefixWord ++ tailWord_2554252).sum := by decide
  have hdescent : baseEnd_2554252 < baseStart_2554252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554315 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 2, 6, 2]
def baseStart_2554315 : Nat := 118140960795 + 2554315 * 2 ^ 59
def prefixEnd_2554315 : Nat := 4983230072969 + 3 ^ 40 * 2554315 * 2
def baseEnd_2554315 : Nat := 1311591337989278964515425

theorem tailTrace_2554315 : CollatzResearch.WordTrace tailWord_2554315 prefixEnd_2554315 1311591337989278964515425 := by
  unfold tailWord_2554315
  simp only [CollatzResearch.WordTrace]
  refine ⟨93163521741160472116088399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62109014494106981410725599 93163521741160472116088399)
  ·
    refine ⟨139745282611740708174132599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93163521741160472116088399 139745282611740708174132599)
    ·
      refine ⟨209617923917611062261198899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139745282611740708174132599 209617923917611062261198899)
      ·
        refine ⟨314426885876416593391798349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209617923917611062261198899 314426885876416593391798349)
        ·
          refine ⟨117910082203656222521924381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 314426885876416593391798349 117910082203656222521924381)
          ·
            refine ⟨44216280826371083445721643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117910082203656222521924381 44216280826371083445721643)
            ·
              refine ⟨66324421239556625168582465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44216280826371083445721643 66324421239556625168582465)
              ·
                refine ⟨49743315929667468876436849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66324421239556625168582465 49743315929667468876436849)
                ·
                  refine ⟨37307486947250601657327637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49743315929667468876436849 37307486947250601657327637)
                  ·
                    refine ⟨1748788450652371952687233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37307486947250601657327637 1748788450652371952687233)
                    ·
                      refine ⟨1311591337989278964515425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1748788450652371952687233 1311591337989278964515425)
                      ·
                        rfl

theorem cell23_2554315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 6, 2].length) (baseStart_2554315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554315 prefixEnd_2554315 := by exact prefixLift 2554315
  have htrace : WordTrace (prefixWord ++ tailWord_2554315) baseStart_2554315 baseEnd_2554315 := by
    simpa [prefixWord, tailWord_2554315, baseEnd_2554315] using wordTrace_append hprefix tailTrace_2554315
  have hstable : (prefixWord ++ tailWord_2554315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554315).length < 2 ^ (prefixWord ++ tailWord_2554315).sum := by decide
  have hdescent : baseEnd_2554315 < baseStart_2554315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554325 : List Nat := [1, 3, 2, 3, 1, 2, 1, 3, 1, 6]
def baseStart_2554325 : Nat := 118140960795 + 2554325 * 2 ^ 59
def prefixEnd_2554325 : Nat := 4983230072969 + 3 ^ 40 * 2554325 * 2
def baseEnd_2554325 : Nat := 437198824265274641796793

theorem tailTrace_2554325 : CollatzResearch.WordTrace tailWord_2554325 prefixEnd_2554325 437198824265274641796793 := by
  unfold tailWord_2554325
  simp only [CollatzResearch.WordTrace]
  refine ⟨93163886471124243823952429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62109257647416162549301619 93163886471124243823952429)
  ·
    refine ⟨34936457426671591433982161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93163886471124243823952429 34936457426671591433982161)
    ·
      refine ⟨26202343070003693575486621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34936457426671591433982161 26202343070003693575486621)
      ·
        refine ⟨9825878651251385090807483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26202343070003693575486621 9825878651251385090807483)
        ·
          refine ⟨14738817976877077636211225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9825878651251385090807483 14738817976877077636211225)
          ·
            refine ⟨11054113482657808227158419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14738817976877077636211225 11054113482657808227158419)
            ·
              refine ⟨16581170223986712340737629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11054113482657808227158419 16581170223986712340737629)
              ·
                refine ⟨6217938833995017127776611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16581170223986712340737629 6217938833995017127776611)
                ·
                  refine ⟨9326908250992525691664917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6217938833995017127776611 9326908250992525691664917)
                  ·
                    refine ⟨437198824265274641796793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9326908250992525691664917 437198824265274641796793)
                    ·
                      rfl

theorem cell23_2554325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_2554325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554325 prefixEnd_2554325 := by exact prefixLift 2554325
  have htrace : WordTrace (prefixWord ++ tailWord_2554325) baseStart_2554325 baseEnd_2554325 := by
    simpa [prefixWord, tailWord_2554325, baseEnd_2554325] using wordTrace_append hprefix tailTrace_2554325
  have hstable : (prefixWord ++ tailWord_2554325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554325).length < 2 ^ (prefixWord ++ tailWord_2554325).sum := by decide
  have hdescent : baseEnd_2554325 < baseStart_2554325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554349 : List Nat := [1, 5, 1, 3, 1, 2, 1, 3, 1, 1, 4]
def baseStart_2554349 : Nat := 118140960795 + 2554349 * 2 ^ 59
def prefixEnd_2554349 : Nat := 4983230072969 + 3 ^ 40 * 2554349 * 2
def baseEnd_2554349 : Nat := 1311608796331531831490269

theorem tailTrace_2554349 : CollatzResearch.WordTrace tailWord_2554349 prefixEnd_2554349 1311608796331531831490269 := by
  unfold tailWord_2554349
  simp only [CollatzResearch.WordTrace]
  refine ⟨93164761823037295922826101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62109841215358197281884067 93164761823037295922826101)
  ·
    refine ⟨8734196420909746492764947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93164761823037295922826101 8734196420909746492764947)
    ·
      refine ⟨13101294631364619739147421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8734196420909746492764947 13101294631364619739147421)
      ·
        refine ⟨4912985486761732402180283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13101294631364619739147421 4912985486761732402180283)
        ·
          refine ⟨7369478230142598603270425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4912985486761732402180283 7369478230142598603270425)
          ·
            refine ⟨5527108672606948952452819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7369478230142598603270425 5527108672606948952452819)
            ·
              refine ⟨8290663008910423428679229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5527108672606948952452819 8290663008910423428679229)
              ·
                refine ⟨3108998628341408785754711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8290663008910423428679229 3108998628341408785754711)
                ·
                  refine ⟨4663497942512113178632067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3108998628341408785754711 4663497942512113178632067)
                  ·
                    refine ⟨6995246913768169767948101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4663497942512113178632067 6995246913768169767948101)
                    ·
                      refine ⟨1311608796331531831490269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6995246913768169767948101 1311608796331531831490269)
                      ·
                        rfl

theorem cell23_2554349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_2554349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554349 prefixEnd_2554349 := by exact prefixLift 2554349
  have htrace : WordTrace (prefixWord ++ tailWord_2554349) baseStart_2554349 baseEnd_2554349 := by
    simpa [prefixWord, tailWord_2554349, baseEnd_2554349] using wordTrace_append hprefix tailTrace_2554349
  have hstable : (prefixWord ++ tailWord_2554349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554349).length < 2 ^ (prefixWord ++ tailWord_2554349).sum := by decide
  have hdescent : baseEnd_2554349 < baseStart_2554349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554352 : List Nat := [2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 3]
def baseStart_2554352 : Nat := 118140960795 + 2554352 * 2 ^ 59
def prefixEnd_2554352 : Nat := 4983230072969 + 3 ^ 40 * 2554352 * 2
def baseEnd_2554352 : Nat := 1311610336773495319752755

theorem tailTrace_2554352 : CollatzResearch.WordTrace tailWord_2554352 prefixEnd_2554352 1311610336773495319752755 := by
  unfold tailWord_2554352
  simp only [CollatzResearch.WordTrace]
  refine ⟨46582435621013213717592655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62109914161350951623456873 46582435621013213717592655)
  ·
    refine ⟨69873653431519820576388983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46582435621013213717592655 69873653431519820576388983)
    ·
      refine ⟨104810480147279730864583475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69873653431519820576388983 104810480147279730864583475)
      ·
        refine ⟨157215720220919596296875213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104810480147279730864583475 157215720220919596296875213)
        ·
          refine ⟨58955895082844848611328205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157215720220919596296875213 58955895082844848611328205)
          ·
            refine ⟨22108460656066818229248077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58955895082844848611328205 22108460656066818229248077)
            ·
              refine ⟨8290672746025056835968029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22108460656066818229248077 8290672746025056835968029)
              ·
                refine ⟨3109002279759396313488011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8290672746025056835968029 3109002279759396313488011)
                ·
                  refine ⟨4663503419639094470232017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3109002279759396313488011 4663503419639094470232017)
                  ·
                    refine ⟨3497627564729320852674013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4663503419639094470232017 3497627564729320852674013)
                    ·
                      refine ⟨1311610336773495319752755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3497627564729320852674013 1311610336773495319752755)
                      ·
                        rfl

theorem cell23_2554352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 3].length) (baseStart_2554352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554352 prefixEnd_2554352 := by exact prefixLift 2554352
  have htrace : WordTrace (prefixWord ++ tailWord_2554352) baseStart_2554352 baseEnd_2554352 := by
    simpa [prefixWord, tailWord_2554352, baseEnd_2554352] using wordTrace_append hprefix tailTrace_2554352
  have hstable : (prefixWord ++ tailWord_2554352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554352).length < 2 ^ (prefixWord ++ tailWord_2554352).sum := by decide
  have hdescent : baseEnd_2554352 < baseStart_2554352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554400 : List Nat := [2, 1, 1, 6, 2, 2, 1, 3, 1, 2, 2]
def baseStart_2554400 : Nat := 118140960795 + 2554400 * 2 ^ 59
def prefixEnd_2554400 : Nat := 4983230072969 + 3 ^ 40 * 2554400 * 2
def baseEnd_2554400 : Nat := 1311634983844911131952535

theorem tailTrace_2554400 : CollatzResearch.WordTrace tailWord_2554400 prefixEnd_2554400 1311634983844911131952535 := by
  unfold tailWord_2554400
  simp only [CollatzResearch.WordTrace]
  refine ⟨46583310972926265816466327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62111081297235021088621769 46583310972926265816466327)
  ·
    refine ⟨69874966459389398724699491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46583310972926265816466327 69874966459389398724699491)
    ·
      refine ⟨104812449689084098087049237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69874966459389398724699491 104812449689084098087049237)
      ·
        refine ⟨4913083579175817097830433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 104812449689084098087049237 4913083579175817097830433)
        ·
          refine ⟨3684812684381862823372825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4913083579175817097830433 3684812684381862823372825)
          ·
            refine ⟨2763609513286397117529619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3684812684381862823372825 2763609513286397117529619)
            ·
              refine ⟨4145414269929595676294429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2763609513286397117529619 4145414269929595676294429)
              ·
                refine ⟨1554530351223598378610411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4145414269929595676294429 1554530351223598378610411)
                ·
                  refine ⟨2331795526835397567915617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1554530351223598378610411 2331795526835397567915617)
                  ·
                    refine ⟨1748846645126548175936713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2331795526835397567915617 1748846645126548175936713)
                    ·
                      refine ⟨1311634983844911131952535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1748846645126548175936713 1311634983844911131952535)
                      ·
                        rfl

theorem cell23_2554400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_2554400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554400 prefixEnd_2554400 := by exact prefixLift 2554400
  have htrace : WordTrace (prefixWord ++ tailWord_2554400) baseStart_2554400 baseEnd_2554400 := by
    simpa [prefixWord, tailWord_2554400, baseEnd_2554400] using wordTrace_append hprefix tailTrace_2554400
  have hstable : (prefixWord ++ tailWord_2554400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554400).length < 2 ^ (prefixWord ++ tailWord_2554400).sum := by decide
  have hdescent : baseEnd_2554400 < baseStart_2554400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554425 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 1, 3, 5]
def baseStart_2554425 : Nat := 118140960795 + 2554425 * 2 ^ 59
def prefixEnd_2554425 : Nat := 4983230072969 + 3 ^ 40 * 2554425 * 2
def baseEnd_2554425 : Nat := 1311647820861273534139919

theorem tailTrace_2554425 : CollatzResearch.WordTrace tailWord_2554425 prefixEnd_2554425 1311647820861273534139919 := by
  unfold tailWord_2554425
  simp only [CollatzResearch.WordTrace]
  refine ⟨93167533770761960902592729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62111689180507973935061819 93167533770761960902592729)
  ·
    refine ⟨69875650328071470676944547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93167533770761960902592729 69875650328071470676944547)
    ·
      refine ⟨104813475492107206015416821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69875650328071470676944547 104813475492107206015416821)
      ·
        refine ⟨9826263327385050563945327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104813475492107206015416821 9826263327385050563945327)
        ·
          refine ⟨14739394991077575845917991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9826263327385050563945327 14739394991077575845917991)
          ·
            refine ⟨22109092486616363768876987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14739394991077575845917991 22109092486616363768876987)
            ·
              refine ⟨33163638729924545653315481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22109092486616363768876987 33163638729924545653315481)
              ·
                refine ⟨24872729047443409239986611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33163638729924545653315481 24872729047443409239986611)
                ·
                  refine ⟨37309093571165113859979917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24872729047443409239986611 37309093571165113859979917)
                  ·
                    refine ⟨13990910089186917697492469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37309093571165113859979917 13990910089186917697492469)
                    ·
                      refine ⟨1311647820861273534139919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13990910089186917697492469 1311647820861273534139919)
                      ·
                        rfl

theorem cell23_2554425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_2554425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554425 prefixEnd_2554425 := by exact prefixLift 2554425
  have htrace : WordTrace (prefixWord ++ tailWord_2554425) baseStart_2554425 baseEnd_2554425 := by
    simpa [prefixWord, tailWord_2554425, baseEnd_2554425] using wordTrace_append hprefix tailTrace_2554425
  have hstable : (prefixWord ++ tailWord_2554425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554425).length < 2 ^ (prefixWord ++ tailWord_2554425).sum := by decide
  have hdescent : baseEnd_2554425 < baseStart_2554425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554433 : List Nat := [1, 2, 5, 1, 1, 4, 2, 1, 2, 1, 3]
def baseStart_2554433 : Nat := 118140960795 + 2554433 * 2 ^ 59
def prefixEnd_2554433 : Nat := 4983230072969 + 3 ^ 40 * 2554433 * 2
def baseEnd_2554433 : Nat := 1311651928706509502839883

theorem tailTrace_2554433 : CollatzResearch.WordTrace tailWord_2554433 prefixEnd_2554433 1311651928706509502839883 := by
  unfold tailWord_2554433
  simp only [CollatzResearch.WordTrace]
  refine ⟨93167825554732978268883953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62111883703155318845922635 93167825554732978268883953)
  ·
    refine ⟨69875869166049733701662965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93167825554732978268883953 69875869166049733701662965)
    ·
      refine ⟨6550862734317162534530903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69875869166049733701662965 6550862734317162534530903)
      ·
        refine ⟨9826294101475743801796355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6550862734317162534530903 9826294101475743801796355)
        ·
          refine ⟨14739441152213615702694533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9826294101475743801796355 14739441152213615702694533)
          ·
            refine ⟨2763645216040052944255225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14739441152213615702694533 2763645216040052944255225)
            ·
              refine ⟨2072733912030039708191419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2763645216040052944255225 2072733912030039708191419)
              ·
                refine ⟨3109100868045059562287129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2072733912030039708191419 3109100868045059562287129)
                ·
                  refine ⟨2331825651033794671715347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3109100868045059562287129 2331825651033794671715347)
                  ·
                    refine ⟨3497738476550692007573021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2331825651033794671715347 3497738476550692007573021)
                    ·
                      refine ⟨1311651928706509502839883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3497738476550692007573021 1311651928706509502839883)
                      ·
                        rfl

theorem cell23_2554433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_2554433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554433 prefixEnd_2554433 := by exact prefixLift 2554433
  have htrace : WordTrace (prefixWord ++ tailWord_2554433) baseStart_2554433 baseEnd_2554433 := by
    simpa [prefixWord, tailWord_2554433, baseEnd_2554433] using wordTrace_append hprefix tailTrace_2554433
  have hstable : (prefixWord ++ tailWord_2554433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554433).length < 2 ^ (prefixWord ++ tailWord_2554433).sum := by decide
  have hdescent : baseEnd_2554433 < baseStart_2554433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554435 : List Nat := [1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 4]
def baseStart_2554435 : Nat := 118140960795 + 2554435 * 2 ^ 59
def prefixEnd_2554435 : Nat := 4983230072969 + 3 ^ 40 * 2554435 * 2
def baseEnd_2554435 : Nat := 1311652955667818495014873

theorem tailTrace_2554435 : CollatzResearch.WordTrace tailWord_2554435 prefixEnd_2554435 1311652955667818495014873 := by
  unfold tailWord_2554435
  simp only [CollatzResearch.WordTrace]
  refine ⟨93167898500725732610456759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62111932333817155073637839 93167898500725732610456759)
  ·
    refine ⟨139751847751088598915685139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93167898500725732610456759 139751847751088598915685139)
    ·
      refine ⟨209627771626632898373527709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139751847751088598915685139 209627771626632898373527709)
      ·
        refine ⟨78610414359987336890072891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209627771626632898373527709 78610414359987336890072891)
        ·
          refine ⟨117915621539981005335109337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78610414359987336890072891 117915621539981005335109337)
          ·
            refine ⟨88436716154985754001332003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117915621539981005335109337 88436716154985754001332003)
            ·
              refine ⟨132655074232478631001998005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88436716154985754001332003 132655074232478631001998005)
              ·
                refine ⟨12436413209294871656437313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 132655074232478631001998005 12436413209294871656437313)
                ·
                  refine ⟨9327309906971153742327985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12436413209294871656437313 9327309906971153742327985)
                  ·
                    refine ⟨6995482430228365306745989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9327309906971153742327985 6995482430228365306745989)
                    ·
                      refine ⟨1311652955667818495014873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6995482430228365306745989 1311652955667818495014873)
                      ·
                        rfl

theorem cell23_2554435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_2554435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554435 prefixEnd_2554435 := by exact prefixLift 2554435
  have htrace : WordTrace (prefixWord ++ tailWord_2554435) baseStart_2554435 baseEnd_2554435 := by
    simpa [prefixWord, tailWord_2554435, baseEnd_2554435] using wordTrace_append hprefix tailTrace_2554435
  have hstable : (prefixWord ++ tailWord_2554435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554435).length < 2 ^ (prefixWord ++ tailWord_2554435).sum := by decide
  have hdescent : baseEnd_2554435 < baseStart_2554435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554475 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 4, 5]
def baseStart_2554475 : Nat := 118140960795 + 2554475 * 2 ^ 59
def prefixEnd_2554475 : Nat := 4983230072969 + 3 ^ 40 * 2554475 * 2
def baseEnd_2554475 : Nat := 437224498297999446171563

theorem tailTrace_2554475 : CollatzResearch.WordTrace tailWord_2554475 prefixEnd_2554475 437224498297999446171563 := by
  unfold tailWord_2554475
  simp only [CollatzResearch.WordTrace]
  refine ⟨93169357420580819441912879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62112904947053879627941919 93169357420580819441912879)
  ·
    refine ⟨139754036130871229162869319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93169357420580819441912879 139754036130871229162869319)
    ·
      refine ⟨209631054196306843744303979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139754036130871229162869319 209631054196306843744303979)
      ·
        refine ⟨314446581294460265616455969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209631054196306843744303979 314446581294460265616455969)
        ·
          refine ⟨235834935970845199212341977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314446581294460265616455969 235834935970845199212341977)
          ·
            refine ⟨176876201978133899409256483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235834935970845199212341977 176876201978133899409256483)
            ·
              refine ⟨265314302967200849113884725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176876201978133899409256483 265314302967200849113884725)
              ·
                refine ⟨24873215903175079604426693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 265314302967200849113884725 24873215903175079604426693)
                ·
                  refine ⟨4663727981845327425830005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24873215903175079604426693 4663727981845327425830005)
                  ·
                    refine ⟨437224498297999446171563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4663727981845327425830005 437224498297999446171563)
                    ·
                      rfl

theorem cell23_2554475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 5].length) (baseStart_2554475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554475 prefixEnd_2554475 := by exact prefixLift 2554475
  have htrace : WordTrace (prefixWord ++ tailWord_2554475) baseStart_2554475 baseEnd_2554475 := by
    simpa [prefixWord, tailWord_2554475, baseEnd_2554475] using wordTrace_append hprefix tailTrace_2554475
  have hstable : (prefixWord ++ tailWord_2554475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554475).length < 2 ^ (prefixWord ++ tailWord_2554475).sum := by decide
  have hdescent : baseEnd_2554475 < baseStart_2554475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554479 : List Nat := [1, 1, 2, 1, 3, 2, 6, 2, 5]
def baseStart_2554479 : Nat := 118140960795 + 2554479 * 2 ^ 59
def prefixEnd_2554479 : Nat := 4983230072969 + 3 ^ 40 * 2554479 * 2
def baseEnd_2554479 : Nat := 145741727646290702540519

theorem tailTrace_2554479 : CollatzResearch.WordTrace tailWord_2554479 prefixEnd_2554479 145741727646290702540519 := by
  unfold tailWord_2554479
  simp only [CollatzResearch.WordTrace]
  refine ⟨93169503312566328125058491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62113002208377552083372327 93169503312566328125058491)
  ·
    refine ⟨139754254968849492187587737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93169503312566328125058491 139754254968849492187587737)
    ·
      refine ⟨104815691226637119140690803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139754254968849492187587737 104815691226637119140690803)
      ·
        refine ⟨157223536839955678711036205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104815691226637119140690803 157223536839955678711036205)
        ·
          refine ⟨58958826314983379516638577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157223536839955678711036205 58958826314983379516638577)
          ·
            refine ⟨44219119736237534637478933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58958826314983379516638577 44219119736237534637478933)
            ·
              refine ⟨2072771237636134436131825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44219119736237534637478933 2072771237636134436131825)
              ·
                refine ⟨1554578428227100827098869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2072771237636134436131825 1554578428227100827098869)
                ·
                  refine ⟨145741727646290702540519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1554578428227100827098869 145741727646290702540519)
                  ·
                    rfl

theorem cell23_2554479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2, 5].length) (baseStart_2554479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554479 prefixEnd_2554479 := by exact prefixLift 2554479
  have htrace : WordTrace (prefixWord ++ tailWord_2554479) baseStart_2554479 baseEnd_2554479 := by
    simpa [prefixWord, tailWord_2554479, baseEnd_2554479] using wordTrace_append hprefix tailTrace_2554479
  have hstable : (prefixWord ++ tailWord_2554479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554479).length < 2 ^ (prefixWord ++ tailWord_2554479).sum := by decide
  have hdescent : baseEnd_2554479 < baseStart_2554479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554549 : List Nat := [1, 3, 3, 3, 1, 1, 1, 2, 1, 4, 3]
def baseStart_2554549 : Nat := 118140960795 + 2554549 * 2 ^ 59
def prefixEnd_2554549 : Nat := 4983230072969 + 3 ^ 40 * 2554549 * 2
def baseEnd_2554549 : Nat := 1311711492462431048989349

theorem tailTrace_2554549 : CollatzResearch.WordTrace tailWord_2554549 prefixEnd_2554549 1311711492462431048989349 := by
  unfold tailWord_2554549
  simp only [CollatzResearch.WordTrace]
  refine ⟨93172056422312730080106701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62114704281541820053404467 93172056422312730080106701)
  ·
    refine ⟨34939521158367273780040013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93172056422312730080106701 34939521158367273780040013)
    ·
      refine ⟨13102320434387727667515005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34939521158367273780040013 13102320434387727667515005)
      ·
        refine ⟨4913370162895397875318127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13102320434387727667515005 4913370162895397875318127)
        ·
          refine ⟨7370055244343096812977191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4913370162895397875318127 7370055244343096812977191)
          ·
            refine ⟨11055082866514645219465787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7370055244343096812977191 11055082866514645219465787)
            ·
              refine ⟨16582624299771967829198681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11055082866514645219465787 16582624299771967829198681)
              ·
                refine ⟨12436968224828975871899011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16582624299771967829198681 12436968224828975871899011)
                ·
                  refine ⟨18655452337243463807848517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12436968224828975871899011 18655452337243463807848517)
                  ·
                    refine ⟨3497897313233149463971597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18655452337243463807848517 3497897313233149463971597)
                    ·
                      refine ⟨1311711492462431048989349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3497897313233149463971597 1311711492462431048989349)
                      ·
                        rfl

theorem cell23_2554549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_2554549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554549 prefixEnd_2554549 := by exact prefixLift 2554549
  have htrace : WordTrace (prefixWord ++ tailWord_2554549) baseStart_2554549 baseEnd_2554549 := by
    simpa [prefixWord, tailWord_2554549, baseEnd_2554549] using wordTrace_append hprefix tailTrace_2554549
  have hstable : (prefixWord ++ tailWord_2554549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554549).length < 2 ^ (prefixWord ++ tailWord_2554549).sum := by decide
  have hdescent : baseEnd_2554549 < baseStart_2554549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554596 : List Nat := [2, 3, 1, 1, 1, 4, 3, 1, 3, 1, 3]
def baseStart_2554596 : Nat := 118140960795 + 2554596 * 2 ^ 59
def prefixEnd_2554596 : Nat := 4983230072969 + 3 ^ 40 * 2554596 * 2
def baseEnd_2554596 : Nat := 1311735626053192365101633

theorem tailTrace_2554596 : CollatzResearch.WordTrace tailWord_2554596 prefixEnd_2554596 1311735626053192365101633 := by
  unfold tailWord_2554596
  simp only [CollatzResearch.WordTrace]
  refine ⟨46586885326571228553533821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62115847102094971404711761 46586885326571228553533821)
  ·
    refine ⟨17470081997464210707575183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46586885326571228553533821 17470081997464210707575183)
    ·
      refine ⟨26205122996196316061362775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17470081997464210707575183 26205122996196316061362775)
      ·
        refine ⟨39307684494294474092044163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26205122996196316061362775 39307684494294474092044163)
        ·
          refine ⟨58961526741441711138066245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39307684494294474092044163 58961526741441711138066245)
          ·
            refine ⟨11055286264020320838387421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58961526741441711138066245 11055286264020320838387421)
            ·
              refine ⟨4145732349007620314395283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11055286264020320838387421 4145732349007620314395283)
              ·
                refine ⟨6218598523511430471592925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4145732349007620314395283 6218598523511430471592925)
                ·
                  refine ⟨2331974446316786426847347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6218598523511430471592925 2331974446316786426847347)
                  ·
                    refine ⟨3497961669475179640271021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2331974446316786426847347 3497961669475179640271021)
                    ·
                      refine ⟨1311735626053192365101633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3497961669475179640271021 1311735626053192365101633)
                      ·
                        rfl

theorem cell23_2554596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_2554596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554596 prefixEnd_2554596 := by exact prefixLift 2554596
  have htrace : WordTrace (prefixWord ++ tailWord_2554596) baseStart_2554596 baseEnd_2554596 := by
    simpa [prefixWord, tailWord_2554596, baseEnd_2554596] using wordTrace_append hprefix tailTrace_2554596
  have hstable : (prefixWord ++ tailWord_2554596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554596).length < 2 ^ (prefixWord ++ tailWord_2554596).sum := by decide
  have hdescent : baseEnd_2554596 < baseStart_2554596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554602 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_2554602 : Nat := 118140960795 + 2554602 * 2 ^ 59
def prefixEnd_2554602 : Nat := 4983230072969 + 3 ^ 40 * 2554602 * 2
def baseEnd_2554602 : Nat := 1311738706937119341626605

theorem tailTrace_2554602 : CollatzResearch.WordTrace tailWord_2554602 prefixEnd_2554602 1311738706937119341626605 := by
  unfold tailWord_2554602
  simp only [CollatzResearch.WordTrace]
  refine ⟨23293497372780180032946515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62115992994080480087857373 23293497372780180032946515)
  ·
    refine ⟨34940246059170270049419773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23293497372780180032946515 34940246059170270049419773)
    ·
      refine ⟨13102592272188851268532415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34940246059170270049419773 13102592272188851268532415)
      ·
        refine ⟨19653888408283276902798623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13102592272188851268532415 19653888408283276902798623)
        ·
          refine ⟨29480832612424915354197935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19653888408283276902798623 29480832612424915354197935)
          ·
            refine ⟨44221248918637373031296903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29480832612424915354197935 44221248918637373031296903)
            ·
              refine ⟨66331873377956059546945355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44221248918637373031296903 66331873377956059546945355)
              ·
                refine ⟨99497810066934089320418033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66331873377956059546945355 99497810066934089320418033)
                ·
                  refine ⟨74623357550200566990313525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99497810066934089320418033 74623357550200566990313525)
                  ·
                    refine ⟨6995939770331303155341893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74623357550200566990313525 6995939770331303155341893)
                    ·
                      refine ⟨1311738706937119341626605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6995939770331303155341893 1311738706937119341626605)
                      ·
                        rfl

theorem cell23_2554602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_2554602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554602 prefixEnd_2554602 := by exact prefixLift 2554602
  have htrace : WordTrace (prefixWord ++ tailWord_2554602) baseStart_2554602 baseEnd_2554602 := by
    simpa [prefixWord, tailWord_2554602, baseEnd_2554602] using wordTrace_append hprefix tailTrace_2554602
  have hstable : (prefixWord ++ tailWord_2554602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554602).length < 2 ^ (prefixWord ++ tailWord_2554602).sum := by decide
  have hdescent : baseEnd_2554602 < baseStart_2554602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554647 : List Nat := [1, 1, 3, 4, 3, 2, 2, 2, 1, 1, 3]
def baseStart_2554647 : Nat := 118140960795 + 2554647 * 2 ^ 59
def prefixEnd_2554647 : Nat := 4983230072969 + 3 ^ 40 * 2554647 * 2
def baseEnd_2554647 : Nat := 1311761813566571665563899

theorem tailTrace_2554647 : CollatzResearch.WordTrace tailWord_2554647 prefixEnd_2554647 1311761813566571665563899 := by
  unfold tailWord_2554647
  simp only [CollatzResearch.WordTrace]
  refine ⟨93175630775957692817174195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62117087183971795211449463 93175630775957692817174195)
  ·
    refine ⟨139763446163936539225761293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93175630775957692817174195 139763446163936539225761293)
    ·
      refine ⟨52411292311476202209660485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139763446163936539225761293 52411292311476202209660485)
      ·
        refine ⟨9827117308401787914311341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52411292311476202209660485 9827117308401787914311341)
        ·
          refine ⟨3685168990650670467866753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9827117308401787914311341 3685168990650670467866753)
          ·
            refine ⟨2763876742988002850900065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3685168990650670467866753 2763876742988002850900065)
            ·
              refine ⟨2072907557241002138175049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2763876742988002850900065 2072907557241002138175049)
              ·
                refine ⟨1554680667930751603631287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2072907557241002138175049 1554680667930751603631287)
                ·
                  refine ⟨2332021001896127405446931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1554680667930751603631287 2332021001896127405446931)
                  ·
                    refine ⟨3498031502844191108170397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2332021001896127405446931 3498031502844191108170397)
                    ·
                      refine ⟨1311761813566571665563899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3498031502844191108170397 1311761813566571665563899)
                      ·
                        rfl

theorem cell23_2554647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_2554647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554647 prefixEnd_2554647 := by exact prefixLift 2554647
  have htrace : WordTrace (prefixWord ++ tailWord_2554647) baseStart_2554647 baseEnd_2554647 := by
    simpa [prefixWord, tailWord_2554647, baseEnd_2554647] using wordTrace_append hprefix tailTrace_2554647
  have hstable : (prefixWord ++ tailWord_2554647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554647).length < 2 ^ (prefixWord ++ tailWord_2554647).sum := by decide
  have hdescent : baseEnd_2554647 < baseStart_2554647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554670 : List Nat := [4, 1, 3, 2, 1, 2, 1, 2, 3, 2, 2]
def baseStart_2554670 : Nat := 118140960795 + 2554670 * 2 ^ 59
def prefixEnd_2554670 : Nat := 4983230072969 + 3 ^ 40 * 2554670 * 2
def baseEnd_2554670 : Nat := 1311773623621625075576293

theorem tailTrace_2554670 : CollatzResearch.WordTrace tailWord_2554670 prefixEnd_2554670 1311773623621625075576293 := by
  unfold tailWord_2554670
  simp only [CollatzResearch.WordTrace]
  refine ⟨11647058706859295968157683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62117646436582911830174309 11647058706859295968157683)
  ·
    refine ⟨17470588060288943952236525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11647058706859295968157683 17470588060288943952236525)
    ·
      refine ⟨6551470522608353982088697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17470588060288943952236525 6551470522608353982088697)
      ·
        refine ⟨4913602891956265486566523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6551470522608353982088697 4913602891956265486566523)
        ·
          refine ⟨7370404337934398229849785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4913602891956265486566523 7370404337934398229849785)
          ·
            refine ⟨5527803253450798672387339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7370404337934398229849785 5527803253450798672387339)
            ·
              refine ⟨8291704880176198008581009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5527803253450798672387339 8291704880176198008581009)
              ·
                refine ⟨6218778660132148506435757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8291704880176198008581009 6218778660132148506435757)
                ·
                  refine ⟨2332041997549555689913409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6218778660132148506435757 2332041997549555689913409)
                  ·
                    refine ⟨1749031498162166767435057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2332041997549555689913409 1749031498162166767435057)
                    ·
                      refine ⟨1311773623621625075576293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1749031498162166767435057 1311773623621625075576293)
                      ·
                        rfl

theorem cell23_2554670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_2554670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554670 prefixEnd_2554670 := by exact prefixLift 2554670
  have htrace : WordTrace (prefixWord ++ tailWord_2554670) baseStart_2554670 baseEnd_2554670 := by
    simpa [prefixWord, tailWord_2554670, baseEnd_2554670] using wordTrace_append hprefix tailTrace_2554670
  have hstable : (prefixWord ++ tailWord_2554670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554670).length < 2 ^ (prefixWord ++ tailWord_2554670).sum := by decide
  have hdescent : baseEnd_2554670 < baseStart_2554670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554816 : List Nat := [2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 4]
def baseStart_2554816 : Nat := 118140960795 + 2554816 * 2 ^ 59
def prefixEnd_2554816 : Nat := 4983230072969 + 3 ^ 40 * 2554816 * 2
def baseEnd_2554816 : Nat := 1311848591797181504350621

theorem tailTrace_2554816 : CollatzResearch.WordTrace tailWord_2554816 prefixEnd_2554816 1311848591797181504350621 := by
  unfold tailWord_2554816
  simp only [CollatzResearch.WordTrace]
  refine ⟨46590897356172717340038151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62121196474896956453384201 46590897356172717340038151)
  ·
    refine ⟨69886346034259076010057227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46590897356172717340038151 69886346034259076010057227)
    ·
      refine ⟨104829519051388614015085841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69886346034259076010057227 104829519051388614015085841)
      ·
        refine ⟨78622139288541460511314381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104829519051388614015085841 78622139288541460511314381)
        ·
          refine ⟨29483302233203047691742893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78622139288541460511314381 29483302233203047691742893)
          ·
            refine ⟨11056238337451142884403585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29483302233203047691742893 11056238337451142884403585)
            ·
              refine ⟨8292178753088357163302689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11056238337451142884403585 8292178753088357163302689)
              ·
                refine ⟨6219134064816267872477017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8292178753088357163302689 6219134064816267872477017)
                ·
                  refine ⟨4664350548612200904357763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6219134064816267872477017 4664350548612200904357763)
                  ·
                    refine ⟨6996525822918301356536645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4664350548612200904357763 6996525822918301356536645)
                    ·
                      refine ⟨1311848591797181504350621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6996525822918301356536645 1311848591797181504350621)
                      ·
                        rfl

theorem cell23_2554816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_2554816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554816 prefixEnd_2554816 := by exact prefixLift 2554816
  have htrace : WordTrace (prefixWord ++ tailWord_2554816) baseStart_2554816 baseEnd_2554816 := by
    simpa [prefixWord, tailWord_2554816, baseEnd_2554816] using wordTrace_append hprefix tailTrace_2554816
  have hstable : (prefixWord ++ tailWord_2554816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554816).length < 2 ^ (prefixWord ++ tailWord_2554816).sum := by decide
  have hdescent : baseEnd_2554816 < baseStart_2554816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554826 : List Nat := [3, 1, 2, 1, 2, 1, 1, 5, 3, 4]
def baseStart_2554826 : Nat := 118140960795 + 2554826 * 2 ^ 59
def prefixEnd_2554826 : Nat := 4983230072969 + 3 ^ 40 * 2554826 * 2
def baseEnd_2554826 : Nat := 437284575534575488408525

theorem tailTrace_2554826 : CollatzResearch.WordTrace tailWord_2554826 prefixEnd_2554826 437284575534575488408525 := by
  unfold tailWord_2554826
  simp only [CollatzResearch.WordTrace]
  refine ⟨23295539860577301596985083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62121439628206137591960221 23295539860577301596985083)
  ·
    refine ⟨34943309790865952395477625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23295539860577301596985083 34943309790865952395477625)
    ·
      refine ⟨26207482343149464296608219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34943309790865952395477625 26207482343149464296608219)
      ·
        refine ⟨39311223514724196444912329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26207482343149464296608219 39311223514724196444912329)
        ·
          refine ⟨29483417636043147333684247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39311223514724196444912329 29483417636043147333684247)
          ·
            refine ⟨44225126454064721000526371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29483417636043147333684247 44225126454064721000526371)
            ·
              refine ⟨66337689681097081500789557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44225126454064721000526371 66337689681097081500789557)
              ·
                refine ⟨6219158407602851390699021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66337689681097081500789557 6219158407602851390699021)
                ·
                  refine ⟨2332184402851069271512133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6219158407602851390699021 2332184402851069271512133)
                  ·
                    refine ⟨437284575534575488408525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2332184402851069271512133 437284575534575488408525)
                    ·
                      rfl

theorem cell23_2554826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_2554826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554826 prefixEnd_2554826 := by exact prefixLift 2554826
  have htrace : WordTrace (prefixWord ++ tailWord_2554826) baseStart_2554826 baseEnd_2554826 := by
    simpa [prefixWord, tailWord_2554826, baseEnd_2554826] using wordTrace_append hprefix tailTrace_2554826
  have hstable : (prefixWord ++ tailWord_2554826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554826).length < 2 ^ (prefixWord ++ tailWord_2554826).sum := by decide
  have hdescent : baseEnd_2554826 < baseStart_2554826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554850 : List Nat := [3, 3, 3, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_2554850 : Nat := 118140960795 + 2554850 * 2 ^ 59
def prefixEnd_2554850 : Nat := 4983230072969 + 3 ^ 40 * 2554850 * 2
def baseEnd_2554850 : Nat := 1311866050139434371325465

theorem tailTrace_2554850 : CollatzResearch.WordTrace tailWord_2554850 prefixEnd_2554850 1311866050139434371325465 := by
  unfold tailWord_2554850
  simp only [CollatzResearch.WordTrace]
  refine ⟨23295758698555564621703501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62122023196148172324542669 23295758698555564621703501)
  ·
    refine ⟨8735909511958336733138813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23295758698555564621703501 8735909511958336733138813)
    ·
      refine ⟨3275966066984376274927055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8735909511958336733138813 3275966066984376274927055)
      ·
        refine ⟨4913949100476564412390583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3275966066984376274927055 4913949100476564412390583)
        ·
          refine ⟨7370923650714846618585875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4913949100476564412390583 7370923650714846618585875)
          ·
            refine ⟨11056385476072269927878813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7370923650714846618585875 11056385476072269927878813)
            ·
              refine ⟨4146144553527101222954555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11056385476072269927878813 4146144553527101222954555)
              ·
                refine ⟨6219216830290651834431833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4146144553527101222954555 6219216830290651834431833)
                ·
                  refine ⟨4664412622717988875823875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6219216830290651834431833 4664412622717988875823875)
                  ·
                    refine ⟨6996618934076983313735813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4664412622717988875823875 6996618934076983313735813)
                    ·
                      refine ⟨1311866050139434371325465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6996618934076983313735813 1311866050139434371325465)
                      ·
                        rfl

theorem cell23_2554850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_2554850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554850 prefixEnd_2554850 := by exact prefixLift 2554850
  have htrace : WordTrace (prefixWord ++ tailWord_2554850) baseStart_2554850 baseEnd_2554850 := by
    simpa [prefixWord, tailWord_2554850, baseEnd_2554850] using wordTrace_append hprefix tailTrace_2554850
  have hstable : (prefixWord ++ tailWord_2554850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554850).length < 2 ^ (prefixWord ++ tailWord_2554850).sum := by decide
  have hdescent : baseEnd_2554850 < baseStart_2554850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554903 : List Nat := [1, 1, 3, 5, 1, 1, 1, 4, 1, 5]
def baseStart_2554903 : Nat := 118140960795 + 2554903 * 2 ^ 59
def prefixEnd_2554903 : Nat := 4983230072969 + 3 ^ 40 * 2554903 * 2
def baseEnd_2554903 : Nat := 437297754871374221320907

theorem tailTrace_2554903 : CollatzResearch.WordTrace tailWord_2554903 prefixEnd_2554903 437297754871374221320907 := by
  unfold tailWord_2554903
  simp only [CollatzResearch.WordTrace]
  refine ⟨93184967863030248538493363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62123311908686832358995575 93184967863030248538493363)
  ·
    refine ⟨139777451794545372807740045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93184967863030248538493363 139777451794545372807740045)
    ·
      refine ⟨52416544422954514802902517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139777451794545372807740045 52416544422954514802902517)
      ·
        refine ⟨4914051039651985762772111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52416544422954514802902517 4914051039651985762772111)
        ·
          refine ⟨7371076559477978644158167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4914051039651985762772111 7371076559477978644158167)
          ·
            refine ⟨11056614839216967966237251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7371076559477978644158167 11056614839216967966237251)
            ·
              refine ⟨16584922258825451949355877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11056614839216967966237251 16584922258825451949355877)
              ·
                refine ⟨3109672923529772240504227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16584922258825451949355877 3109672923529772240504227)
                ·
                  refine ⟨4664509385294658360756341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3109672923529772240504227 4664509385294658360756341)
                  ·
                    refine ⟨437297754871374221320907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4664509385294658360756341 437297754871374221320907)
                    ·
                      rfl

theorem cell23_2554903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 5].length) (baseStart_2554903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554903 prefixEnd_2554903 := by exact prefixLift 2554903
  have htrace : WordTrace (prefixWord ++ tailWord_2554903) baseStart_2554903 baseEnd_2554903 := by
    simpa [prefixWord, tailWord_2554903, baseEnd_2554903] using wordTrace_append hprefix tailTrace_2554903
  have hstable : (prefixWord ++ tailWord_2554903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554903).length < 2 ^ (prefixWord ++ tailWord_2554903).sum := by decide
  have hdescent : baseEnd_2554903 < baseStart_2554903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554933 : List Nat := [1, 3, 3, 1, 1, 1, 1, 6, 2, 4]
def baseStart_2554933 : Nat := 118140960795 + 2554933 * 2 ^ 59
def prefixEnd_2554933 : Nat := 4983230072969 + 3 ^ 40 * 2554933 * 2
def baseEnd_2554933 : Nat := 437302889677919182195861

theorem tailTrace_2554933 : CollatzResearch.WordTrace tailWord_2554933 prefixEnd_2554933 437302889677919182195861 := by
  unfold tailWord_2554933
  simp only [CollatzResearch.WordTrace]
  refine ⟨93186062052921563662085453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62124041368614375774723635 93186062052921563662085453)
  ·
    refine ⟨34944773269845586373282045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93186062052921563662085453 34944773269845586373282045)
    ·
      refine ⟨13104289976192094889980767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34944773269845586373282045 13104289976192094889980767)
      ·
        refine ⟨19656434964288142334971151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13104289976192094889980767 19656434964288142334971151)
        ·
          refine ⟨29484652446432213502456727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19656434964288142334971151 29484652446432213502456727)
          ·
            refine ⟨44226978669648320253685091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29484652446432213502456727 44226978669648320253685091)
            ·
              refine ⟨66340468004472480380527637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44226978669648320253685091 66340468004472480380527637)
              ·
                refine ⟨3109709437709647517837233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66340468004472480380527637 3109709437709647517837233)
                ·
                  refine ⟨2332282078282235638377925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3109709437709647517837233 2332282078282235638377925)
                  ·
                    refine ⟨437302889677919182195861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2332282078282235638377925 437302889677919182195861)
                    ·
                      rfl

theorem cell23_2554933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_2554933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554933 prefixEnd_2554933 := by exact prefixLift 2554933
  have htrace : WordTrace (prefixWord ++ tailWord_2554933) baseStart_2554933 baseEnd_2554933 := by
    simpa [prefixWord, tailWord_2554933, baseEnd_2554933] using wordTrace_append hprefix tailTrace_2554933
  have hstable : (prefixWord ++ tailWord_2554933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554933).length < 2 ^ (prefixWord ++ tailWord_2554933).sum := by decide
  have hdescent : baseEnd_2554933 < baseStart_2554933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554936 : List Nat := [2, 1, 2, 1, 5, 1, 1, 2, 1, 1, 6]
def baseStart_2554936 : Nat := 118140960795 + 2554936 * 2 ^ 59
def prefixEnd_2554936 : Nat := 4983230072969 + 3 ^ 40 * 2554936 * 2
def baseEnd_2554936 : Nat := 1311910209475721034850069

theorem tailTrace_2554936 : CollatzResearch.WordTrace tailWord_2554936 prefixEnd_2554936 1311910209475721034850069 := by
  unfold tailWord_2554936
  simp only [CollatzResearch.WordTrace]
  refine ⟨46593085735955347587222331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62124114314607130116296441 46593085735955347587222331)
  ·
    refine ⟨69889628603933021380833497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46593085735955347587222331 69889628603933021380833497)
    ·
      refine ⟨52417221452949766035625123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69889628603933021380833497 52417221452949766035625123)
      ·
        refine ⟨78625832179424649053437685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52417221452949766035625123 78625832179424649053437685)
        ·
          refine ⟨7371171766821060848759783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78625832179424649053437685 7371171766821060848759783)
          ·
            refine ⟨11056757650231591273139675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7371171766821060848759783 11056757650231591273139675)
            ·
              refine ⟨16585136475347386909709513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11056757650231591273139675 16585136475347386909709513)
              ·
                refine ⟨12438852356510540182282135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16585136475347386909709513 12438852356510540182282135)
                ·
                  refine ⟨18658278534765810273423203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12438852356510540182282135 18658278534765810273423203)
                  ·
                    refine ⟨27987417802148715410134805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18658278534765810273423203 27987417802148715410134805)
                    ·
                      refine ⟨1311910209475721034850069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27987417802148715410134805 1311910209475721034850069)
                      ·
                        rfl

theorem cell23_2554936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_2554936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554936 prefixEnd_2554936 := by exact prefixLift 2554936
  have htrace : WordTrace (prefixWord ++ tailWord_2554936) baseStart_2554936 baseEnd_2554936 := by
    simpa [prefixWord, tailWord_2554936, baseEnd_2554936] using wordTrace_append hprefix tailTrace_2554936
  have hstable : (prefixWord ++ tailWord_2554936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554936).length < 2 ^ (prefixWord ++ tailWord_2554936).sum := by decide
  have hdescent : baseEnd_2554936 < baseStart_2554936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554939 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 7]
def baseStart_2554939 : Nat := 118140960795 + 2554939 * 2 ^ 59
def prefixEnd_2554939 : Nat := 4983230072969 + 3 ^ 40 * 2554939 * 2
def baseEnd_2554939 : Nat := 1311911749917684523112555

theorem tailTrace_2554939 : CollatzResearch.WordTrace tailWord_2554939 prefixEnd_2554939 1311911749917684523112555 := by
  unfold tailWord_2554939
  simp only [CollatzResearch.WordTrace]
  refine ⟨93186280890899826686803871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62124187260599884457869247 93186280890899826686803871)
  ·
    refine ⟨139779421336349740030205807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93186280890899826686803871 139779421336349740030205807)
    ·
      refine ⟨209669132004524610045308711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139779421336349740030205807 209669132004524610045308711)
      ·
        refine ⟨314503698006786915067963067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209669132004524610045308711 314503698006786915067963067)
        ·
          refine ⟨471755547010180372601944601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314503698006786915067963067 471755547010180372601944601)
          ·
            refine ⟨353816660257635279451458451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 471755547010180372601944601 353816660257635279451458451)
            ·
              refine ⟨530724990386452919177187677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353816660257635279451458451 530724990386452919177187677)
              ·
                refine ⟨199021871394919844691445379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 530724990386452919177187677 199021871394919844691445379)
                ·
                  refine ⟨298532807092379767037168069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 199021871394919844691445379 298532807092379767037168069)
                  ·
                    refine ⟨55974901329821206319469013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 298532807092379767037168069 55974901329821206319469013)
                    ·
                      refine ⟨1311911749917684523112555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55974901329821206319469013 1311911749917684523112555)
                      ·
                        rfl

theorem cell23_2554939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 7].length) (baseStart_2554939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554939 prefixEnd_2554939 := by exact prefixLift 2554939
  have htrace : WordTrace (prefixWord ++ tailWord_2554939) baseStart_2554939 baseEnd_2554939 := by
    simpa [prefixWord, tailWord_2554939, baseEnd_2554939] using wordTrace_append hprefix tailTrace_2554939
  have hstable : (prefixWord ++ tailWord_2554939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554939).length < 2 ^ (prefixWord ++ tailWord_2554939).sum := by decide
  have hdescent : baseEnd_2554939 < baseStart_2554939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554957 : List Nat := [1, 6, 1, 1, 1, 4, 1, 2, 1, 1, 4]
def baseStart_2554957 : Nat := 118140960795 + 2554957 * 2 ^ 59
def prefixEnd_2554957 : Nat := 4983230072969 + 3 ^ 40 * 2554957 * 2
def baseEnd_2554957 : Nat := 1311920992569465452687473

theorem tailTrace_2554957 : CollatzResearch.WordTrace tailWord_2554957 prefixEnd_2554957 1311920992569465452687473 := by
  unfold tailWord_2554957
  simp only [CollatzResearch.WordTrace]
  refine ⟨93186937404834615760959125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62124624936556410507306083 93186937404834615760959125)
  ·
    refine ⟨4368137690851622613794959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93186937404834615760959125 4368137690851622613794959)
    ·
      refine ⟨6552206536277433920692439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4368137690851622613794959 6552206536277433920692439)
      ·
        refine ⟨9828309804416150881038659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6552206536277433920692439 9828309804416150881038659)
        ·
          refine ⟨14742464706624226321557989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9828309804416150881038659 14742464706624226321557989)
          ·
            refine ⟨2764212132492042435292123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14742464706624226321557989 2764212132492042435292123)
            ·
              refine ⟨4146318198738063652938185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2764212132492042435292123 4146318198738063652938185)
              ·
                refine ⟨3109738649053547739703639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4146318198738063652938185 3109738649053547739703639)
                ·
                  refine ⟨4664607973580321609555459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3109738649053547739703639 4664607973580321609555459)
                  ·
                    refine ⟨6996911960370482414333189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4664607973580321609555459 6996911960370482414333189)
                    ·
                      refine ⟨1311920992569465452687473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6996911960370482414333189 1311920992569465452687473)
                      ·
                        rfl

theorem cell23_2554957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_2554957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554957 prefixEnd_2554957 := by exact prefixLift 2554957
  have htrace : WordTrace (prefixWord ++ tailWord_2554957) baseStart_2554957 baseEnd_2554957 := by
    simpa [prefixWord, tailWord_2554957, baseEnd_2554957] using wordTrace_append hprefix tailTrace_2554957
  have hstable : (prefixWord ++ tailWord_2554957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554957).length < 2 ^ (prefixWord ++ tailWord_2554957).sum := by decide
  have hdescent : baseEnd_2554957 < baseStart_2554957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2554997 : List Nat := [1, 3, 4, 3, 2, 1, 1, 8]
def baseStart_2554997 : Nat := 118140960795 + 2554997 * 2 ^ 59
def prefixEnd_2554997 : Nat := 4983230072969 + 3 ^ 40 * 2554997 * 2
def baseEnd_2554997 : Nat := 48590427103542418377307

theorem tailTrace_2554997 : CollatzResearch.WordTrace tailWord_2554997 prefixEnd_2554997 48590427103542418377307 := by
  unfold tailWord_2554997
  simp only [CollatzResearch.WordTrace]
  refine ⟨93188396324689702592415245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62125597549793135061610163 93188396324689702592415245)
  ·
    refine ⟨34945648621758638472155717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93188396324689702592415245 34945648621758638472155717)
    ·
      refine ⟨6552309116579744713529197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34945648621758638472155717 6552309116579744713529197)
      ·
        refine ⟨2457115918717404267573449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6552309116579744713529197 2457115918717404267573449)
        ·
          refine ⟨1842836939038053200680087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2457115918717404267573449 1842836939038053200680087)
          ·
            refine ⟨2764255408557079801020131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1842836939038053200680087 2764255408557079801020131)
            ·
              refine ⟨4146383112835619701530197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2764255408557079801020131 4146383112835619701530197)
              ·
                refine ⟨48590427103542418377307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4146383112835619701530197 48590427103542418377307)
                ·
                  rfl

theorem cell23_2554997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 8].length) (baseStart_2554997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2554997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2554997 prefixEnd_2554997 := by exact prefixLift 2554997
  have htrace : WordTrace (prefixWord ++ tailWord_2554997) baseStart_2554997 baseEnd_2554997 := by
    simpa [prefixWord, tailWord_2554997, baseEnd_2554997] using wordTrace_append hprefix tailTrace_2554997
  have hstable : (prefixWord ++ tailWord_2554997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2554997).length < 2 ^ (prefixWord ++ tailWord_2554997).sum := by decide
  have hdescent : baseEnd_2554997 < baseStart_2554997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2554997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555034 : List Nat := [3, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2]
def baseStart_2555034 : Nat := 118140960795 + 2555034 * 2 ^ 59
def prefixEnd_2555034 : Nat := 4983230072969 + 3 ^ 40 * 2555034 * 2
def baseEnd_2555034 : Nat := 1311960530579861651424619

theorem tailTrace_2555034 : CollatzResearch.WordTrace tailWord_2555034 prefixEnd_2555034 1311960530579861651424619 := by
  unfold tailWord_2555034
  simp only [CollatzResearch.WordTrace]
  refine ⟨23297436456388914477878039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62126497217037105274341437 23297436456388914477878039)
  ·
    refine ⟨34946154684583371716817059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23297436456388914477878039 34946154684583371716817059)
    ·
      refine ⟨52419232026875057575225589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34946154684583371716817059 52419232026875057575225589)
      ·
        refine ⟨4914303002519536647677399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52419232026875057575225589 4914303002519536647677399)
        ·
          refine ⟨7371454503779304971516099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4914303002519536647677399 7371454503779304971516099)
          ·
            refine ⟨11057181755668957457274149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7371454503779304971516099 11057181755668957457274149)
            ·
              refine ⟨2073221579187929523238903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11057181755668957457274149 2073221579187929523238903)
              ·
                refine ⟨3109832368781894284858355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2073221579187929523238903 3109832368781894284858355)
                ·
                  refine ⟨4664748553172841427287533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3109832368781894284858355 4664748553172841427287533)
                  ·
                    refine ⟨1749280707439815535232825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4664748553172841427287533 1749280707439815535232825)
                    ·
                      refine ⟨1311960530579861651424619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1749280707439815535232825 1311960530579861651424619)
                      ·
                        rfl

theorem cell23_2555034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_2555034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555034 prefixEnd_2555034 := by exact prefixLift 2555034
  have htrace : WordTrace (prefixWord ++ tailWord_2555034) baseStart_2555034 baseEnd_2555034 := by
    simpa [prefixWord, tailWord_2555034, baseEnd_2555034] using wordTrace_append hprefix tailTrace_2555034
  have hstable : (prefixWord ++ tailWord_2555034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555034).length < 2 ^ (prefixWord ++ tailWord_2555034).sum := by decide
  have hdescent : baseEnd_2555034 < baseStart_2555034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555063 : List Nat := [1, 1, 3, 1, 4, 1, 1, 3, 2, 3, 3]
def baseStart_2555063 : Nat := 118140960795 + 2555063 * 2 ^ 59
def prefixEnd_2555063 : Nat := 4983230072969 + 3 ^ 40 * 2555063 * 2
def baseEnd_2555063 : Nat := 1311975421518842037961985

theorem tailTrace_2555063 : CollatzResearch.WordTrace tailWord_2555063 prefixEnd_2555063 1311975421518842037961985 := by
  unfold tailWord_2555063
  simp only [CollatzResearch.WordTrace]
  refine ⟨93190803542450595864317843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62127202361633730576211895 93190803542450595864317843)
  ·
    refine ⟨139786205313675893796476765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93190803542450595864317843 139786205313675893796476765)
    ·
      refine ⟨52419826992628460173678787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139786205313675893796476765 52419826992628460173678787)
      ·
        refine ⟨78629740488942690260518181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52419826992628460173678787 78629740488942690260518181)
        ·
          refine ⟨14743076341676754423847159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78629740488942690260518181 14743076341676754423847159)
          ·
            refine ⟨22114614512515131635770739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14743076341676754423847159 22114614512515131635770739)
            ·
              refine ⟨33171921768772697453656109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22114614512515131635770739 33171921768772697453656109)
              ·
                refine ⟨12439470663289761545121041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33171921768772697453656109 12439470663289761545121041)
                ·
                  refine ⟨9329602997467321158840781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12439470663289761545121041 9329602997467321158840781)
                  ·
                    refine ⟨3498601124050245434565293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9329602997467321158840781 3498601124050245434565293)
                    ·
                      refine ⟨1311975421518842037961985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3498601124050245434565293 1311975421518842037961985)
                      ·
                        rfl

theorem cell23_2555063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3, 3].length) (baseStart_2555063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555063 prefixEnd_2555063 := by exact prefixLift 2555063
  have htrace : WordTrace (prefixWord ++ tailWord_2555063) baseStart_2555063 baseEnd_2555063 := by
    simpa [prefixWord, tailWord_2555063, baseEnd_2555063] using wordTrace_append hprefix tailTrace_2555063
  have hstable : (prefixWord ++ tailWord_2555063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555063).length < 2 ^ (prefixWord ++ tailWord_2555063).sum := by decide
  have hdescent : baseEnd_2555063 < baseStart_2555063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555103 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 4]
def baseStart_2555103 : Nat := 118140960795 + 2555103 * 2 ^ 59
def prefixEnd_2555103 : Nat := 4983230072969 + 3 ^ 40 * 2555103 * 2
def baseEnd_2555103 : Nat := 1311995960745021881461801

theorem tailTrace_2555103 : CollatzResearch.WordTrace tailWord_2555103 prefixEnd_2555103 1311995960745021881461801 := by
  unfold tailWord_2555103
  simp only [CollatzResearch.WordTrace]
  refine ⟨93192262462305682695773963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62128174974870455130515975 93192262462305682695773963)
  ·
    refine ⟨139788393693458524043660945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93192262462305682695773963 139788393693458524043660945)
    ·
      refine ⟨104841295270093893032745709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139788393693458524043660945 104841295270093893032745709)
      ·
        refine ⟨39315485726285209887279641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104841295270093893032745709 39315485726285209887279641)
        ·
          refine ⟨29486614294713907415459731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39315485726285209887279641 29486614294713907415459731)
          ·
            refine ⟨44229921442070861123189597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29486614294713907415459731 44229921442070861123189597)
            ·
              refine ⟨16586220540776572921196099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44229921442070861123189597 16586220540776572921196099)
              ·
                refine ⟨24879330811164859381794149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16586220540776572921196099 24879330811164859381794149)
                ·
                  refine ⟨4664874527093411134086403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24879330811164859381794149 4664874527093411134086403)
                  ·
                    refine ⟨6997311790640116701129605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4664874527093411134086403 6997311790640116701129605)
                    ·
                      refine ⟨1311995960745021881461801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6997311790640116701129605 1311995960745021881461801)
                      ·
                        rfl

theorem cell23_2555103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_2555103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555103 prefixEnd_2555103 := by exact prefixLift 2555103
  have htrace : WordTrace (prefixWord ++ tailWord_2555103) baseStart_2555103 baseEnd_2555103 := by
    simpa [prefixWord, tailWord_2555103, baseEnd_2555103] using wordTrace_append hprefix tailTrace_2555103
  have hstable : (prefixWord ++ tailWord_2555103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555103).length < 2 ^ (prefixWord ++ tailWord_2555103).sum := by decide
  have hdescent : baseEnd_2555103 < baseStart_2555103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555160 : List Nat := [2, 1, 2, 3, 1, 4, 2, 2, 6]
def baseStart_2555160 : Nat := 118140960795 + 2555160 * 2 ^ 59
def prefixEnd_2555160 : Nat := 4983230072969 + 3 ^ 40 * 2555160 * 2
def baseEnd_2555160 : Nat := 145780581015814239827671

theorem tailTrace_2555160 : CollatzResearch.WordTrace tailWord_2555160 prefixEnd_2555160 145780581015814239827671 := by
  unfold tailWord_2555160
  simp only [CollatzResearch.WordTrace]
  refine ⟨46597170711549590715299467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62129560948732787620399289 46597170711549590715299467)
  ·
    refine ⟨69895756067324386072949201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46597170711549590715299467 69895756067324386072949201)
    ·
      refine ⟨52421817050493289554711901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69895756067324386072949201 52421817050493289554711901)
      ·
        refine ⟨19658181393934983583016963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52421817050493289554711901 19658181393934983583016963)
        ·
          refine ⟨29487272090902475374525445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19658181393934983583016963 29487272090902475374525445)
          ·
            refine ⟨5528863517044214132723521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29487272090902475374525445 5528863517044214132723521)
            ·
              refine ⟨4146647637783160599542641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5528863517044214132723521 4146647637783160599542641)
              ·
                refine ⟨3109985728337370449656981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4146647637783160599542641 3109985728337370449656981)
                ·
                  refine ⟨145780581015814239827671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3109985728337370449656981 145780581015814239827671)
                  ·
                    rfl

theorem cell23_2555160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 6].length) (baseStart_2555160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555160 prefixEnd_2555160 := by exact prefixLift 2555160
  have htrace : WordTrace (prefixWord ++ tailWord_2555160) baseStart_2555160 baseEnd_2555160 := by
    simpa [prefixWord, tailWord_2555160, baseEnd_2555160] using wordTrace_append hprefix tailTrace_2555160
  have hstable : (prefixWord ++ tailWord_2555160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555160).length < 2 ^ (prefixWord ++ tailWord_2555160).sum := by decide
  have hdescent : baseEnd_2555160 < baseStart_2555160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555164 : List Nat := [2, 2, 3, 1, 1, 1, 6, 2, 1, 4]
def baseStart_2555164 : Nat := 118140960795 + 2555164 * 2 ^ 59
def prefixEnd_2555164 : Nat := 4983230072969 + 3 ^ 40 * 2555164 * 2
def baseEnd_2555164 : Nat := 437342427688315380933007

theorem tailTrace_2555164 : CollatzResearch.WordTrace tailWord_2555164 prefixEnd_2555164 437342427688315380933007 := by
  unfold tailWord_2555164
  simp only [CollatzResearch.WordTrace]
  refine ⟨46597243657542345056872273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62129658210056460075829697 46597243657542345056872273)
  ·
    refine ⟨34947932743156758792654205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46597243657542345056872273 34947932743156758792654205)
    ·
      refine ⟨13105474778683784547245327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34947932743156758792654205 13105474778683784547245327)
      ·
        refine ⟨19658212168025676820867991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13105474778683784547245327 19658212168025676820867991)
        ·
          refine ⟨29487318252038515231301987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19658212168025676820867991 29487318252038515231301987)
          ·
            refine ⟨44230977378057772846952981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29487318252038515231301987 44230977378057772846952981)
            ·
              refine ⟨2073327064596458102200921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44230977378057772846952981 2073327064596458102200921)
              ·
                refine ⟨1554995298447343576650691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2073327064596458102200921 1554995298447343576650691)
                ·
                  refine ⟨2332492947671015364976037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1554995298447343576650691 2332492947671015364976037)
                  ·
                    refine ⟨437342427688315380933007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2332492947671015364976037 437342427688315380933007)
                    ·
                      rfl

theorem cell23_2555164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_2555164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555164 prefixEnd_2555164 := by exact prefixLift 2555164
  have htrace : WordTrace (prefixWord ++ tailWord_2555164) baseStart_2555164 baseEnd_2555164 := by
    simpa [prefixWord, tailWord_2555164, baseEnd_2555164] using wordTrace_append hprefix tailTrace_2555164
  have hstable : (prefixWord ++ tailWord_2555164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555164).length < 2 ^ (prefixWord ++ tailWord_2555164).sum := by decide
  have hdescent : baseEnd_2555164 < baseStart_2555164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555180 : List Nat := [2, 2, 1, 1, 1, 3, 1, 4, 1, 5, 2]
def baseStart_2555180 : Nat := 118140960795 + 2555180 * 2 ^ 59
def prefixEnd_2555180 : Nat := 4983230072969 + 3 ^ 40 * 2555180 * 2
def baseEnd_2555180 : Nat := 1312035498755418080198947

theorem tailTrace_2555180 : CollatzResearch.WordTrace tailWord_2555180 prefixEnd_2555180 1312035498755418080198947 := by
  unfold tailWord_2555180
  simp only [CollatzResearch.WordTrace]
  refine ⟨46597535441513362423163497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62130047255351149897551329 46597535441513362423163497)
  ·
    refine ⟨34948151581135021817372623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46597535441513362423163497 34948151581135021817372623)
    ·
      refine ⟨52422227371702532726058935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34948151581135021817372623 52422227371702532726058935)
      ·
        refine ⟨78633341057553799089088403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52422227371702532726058935 78633341057553799089088403)
        ·
          refine ⟨117950011586330698633632605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78633341057553799089088403 117950011586330698633632605)
          ·
            refine ⟨44231254344874011987612227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117950011586330698633632605 44231254344874011987612227)
            ·
              refine ⟨66346881517311017981418341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44231254344874011987612227 66346881517311017981418341)
              ·
                refine ⟨12440040284495815871515939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66346881517311017981418341 12440040284495815871515939)
                ·
                  refine ⟨18660060426743723807273909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12440040284495815871515939 18660060426743723807273909)
                  ·
                    refine ⟨1749380665007224106931929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18660060426743723807273909 1749380665007224106931929)
                    ·
                      refine ⟨1312035498755418080198947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1749380665007224106931929 1312035498755418080198947)
                      ·
                        rfl

theorem cell23_2555180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 5, 2].length) (baseStart_2555180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555180 prefixEnd_2555180 := by exact prefixLift 2555180
  have htrace : WordTrace (prefixWord ++ tailWord_2555180) baseStart_2555180 baseEnd_2555180 := by
    simpa [prefixWord, tailWord_2555180, baseEnd_2555180] using wordTrace_append hprefix tailTrace_2555180
  have hstable : (prefixWord ++ tailWord_2555180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555180).length < 2 ^ (prefixWord ++ tailWord_2555180).sum := by decide
  have hdescent : baseEnd_2555180 < baseStart_2555180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555187 : List Nat := [1, 1, 1, 2, 5, 3, 1, 2, 3, 1, 3]
def baseStart_2555187 : Nat := 118140960795 + 2555187 * 2 ^ 59
def prefixEnd_2555187 : Nat := 4983230072969 + 3 ^ 40 * 2555187 * 2
def baseEnd_2555187 : Nat := 1312039093119999552811415

theorem tailTrace_2555187 : CollatzResearch.WordTrace tailWord_2555187 prefixEnd_2555187 1312039093119999552811415 := by
  unfold tailWord_2555187
  simp only [CollatzResearch.WordTrace]
  refine ⟨93195326194001365041831815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62130217462667576694554543 93195326194001365041831815)
  ·
    refine ⟨139792989291002047562747723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93195326194001365041831815 139792989291002047562747723)
    ·
      refine ⟨209689483936503071344121585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139792989291002047562747723 209689483936503071344121585)
      ·
        refine ⟨157267112952377303508091189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209689483936503071344121585 157267112952377303508091189)
        ·
          refine ⟨14743791839285372203883549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 157267112952377303508091189 14743791839285372203883549)
          ·
            refine ⟨5528921939732014576456331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14743791839285372203883549 5528921939732014576456331)
            ·
              refine ⟨8293382909598021864684497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5528921939732014576456331 8293382909598021864684497)
              ·
                refine ⟨6220037182198516398513373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8293382909598021864684497 6220037182198516398513373)
                ·
                  refine ⟨2332513943324443649442515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6220037182198516398513373 2332513943324443649442515)
                  ·
                    refine ⟨3498770914986665474163773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2332513943324443649442515 3498770914986665474163773)
                    ·
                      refine ⟨1312039093119999552811415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3498770914986665474163773 1312039093119999552811415)
                      ·
                        rfl

theorem cell23_2555187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3, 1, 3].length) (baseStart_2555187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555187 prefixEnd_2555187 := by exact prefixLift 2555187
  have htrace : WordTrace (prefixWord ++ tailWord_2555187) baseStart_2555187 baseEnd_2555187 := by
    simpa [prefixWord, tailWord_2555187, baseEnd_2555187] using wordTrace_append hprefix tailTrace_2555187
  have hstable : (prefixWord ++ tailWord_2555187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555187).length < 2 ^ (prefixWord ++ tailWord_2555187).sum := by decide
  have hdescent : baseEnd_2555187 < baseStart_2555187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555207 : List Nat := [1, 1, 4, 1, 2, 3, 4, 1, 1, 5]
def baseStart_2555207 : Nat := 118140960795 + 2555207 * 2 ^ 59
def prefixEnd_2555207 : Nat := 4983230072969 + 3 ^ 40 * 2555207 * 2
def baseEnd_2555207 : Nat := 437349787577696491520441

theorem tailTrace_2555207 : CollatzResearch.WordTrace tailWord_2555207 prefixEnd_2555207 437349787577696491520441 := by
  unfold tailWord_2555207
  simp only [CollatzResearch.WordTrace]
  refine ⟨93196055653928908457559875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62130703769285938971706583 93196055653928908457559875)
  ·
    refine ⟨139794083480893362686339813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93196055653928908457559875 139794083480893362686339813)
    ·
      refine ⟨26211390652667505503688715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139794083480893362686339813 26211390652667505503688715)
      ·
        refine ⟨39317085979001258255533073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26211390652667505503688715 39317085979001258255533073)
        ·
          refine ⟨29487814484250943691649805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39317085979001258255533073 29487814484250943691649805)
          ·
            refine ⟨11057930431594103884368677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29487814484250943691649805 11057930431594103884368677)
            ·
              refine ⟨2073361955923894478319127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11057930431594103884368677 2073361955923894478319127)
              ·
                refine ⟨3110042933885841717478691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2073361955923894478319127 3110042933885841717478691)
                ·
                  refine ⟨4665064400828762576218037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3110042933885841717478691 4665064400828762576218037)
                  ·
                    refine ⟨437349787577696491520441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4665064400828762576218037 437349787577696491520441)
                    ·
                      rfl

theorem cell23_2555207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_2555207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555207 prefixEnd_2555207 := by exact prefixLift 2555207
  have htrace : WordTrace (prefixWord ++ tailWord_2555207) baseStart_2555207 baseEnd_2555207 := by
    simpa [prefixWord, tailWord_2555207, baseEnd_2555207] using wordTrace_append hprefix tailTrace_2555207
  have hstable : (prefixWord ++ tailWord_2555207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555207).length < 2 ^ (prefixWord ++ tailWord_2555207).sum := by decide
  have hdescent : baseEnd_2555207 < baseStart_2555207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555210 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 1, 8, 2]
def baseStart_2555210 : Nat := 118140960795 + 2555210 * 2 ^ 59
def prefixEnd_2555210 : Nat := 4983230072969 + 3 ^ 40 * 2555210 * 2
def baseEnd_2555210 : Nat := 1312050903175052962823809

theorem tailTrace_2555210 : CollatzResearch.WordTrace tailWord_2555210 prefixEnd_2555210 1312050903175052962823809 := by
  unfold tailWord_2555210
  simp only [CollatzResearch.WordTrace]
  refine ⟨23299041268229509992479771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62130776715278693313279389 23299041268229509992479771)
  ·
    refine ⟨34948561902344264988719657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23299041268229509992479771 34948561902344264988719657)
    ·
      refine ⟨26211421426758198741539743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34948561902344264988719657 26211421426758198741539743)
      ·
        refine ⟨39317132140137298112309615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26211421426758198741539743 39317132140137298112309615)
        ·
          refine ⟨58975698210205947168464423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39317132140137298112309615 58975698210205947168464423)
          ·
            refine ⟨88463547315308920752696635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58975698210205947168464423 88463547315308920752696635)
            ·
              refine ⟨132695320972963381129044953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88463547315308920752696635 132695320972963381129044953)
              ·
                refine ⟨99521490729722535846783715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132695320972963381129044953 99521490729722535846783715)
                ·
                  refine ⟨149282236094583803770175573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99521490729722535846783715 149282236094583803770175573)
                  ·
                    refine ⟨1749401204233403950431745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 149282236094583803770175573 1749401204233403950431745)
                    ·
                      refine ⟨1312050903175052962823809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1749401204233403950431745 1312050903175052962823809)
                      ·
                        rfl

theorem cell23_2555210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 1, 8, 2].length) (baseStart_2555210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555210 prefixEnd_2555210 := by exact prefixLift 2555210
  have htrace : WordTrace (prefixWord ++ tailWord_2555210) baseStart_2555210 baseEnd_2555210 := by
    simpa [prefixWord, tailWord_2555210, baseEnd_2555210] using wordTrace_append hprefix tailTrace_2555210
  have hstable : (prefixWord ++ tailWord_2555210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555210).length < 2 ^ (prefixWord ++ tailWord_2555210).sum := by decide
  have hdescent : baseEnd_2555210 < baseStart_2555210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555244 : List Nat := [2, 2, 1, 1, 5, 1, 2, 2, 3, 2, 2]
def baseStart_2555244 : Nat := 118140960795 + 2555244 * 2 ^ 59
def prefixEnd_2555244 : Nat := 4983230072969 + 3 ^ 40 * 2555244 * 2
def baseEnd_2555244 : Nat := 1312068361517305829798653

theorem tailTrace_2555244 : CollatzResearch.WordTrace tailWord_2555244 prefixEnd_2555244 1312068361517305829798653 := by
  unfold tailWord_2555244
  simp only [CollatzResearch.WordTrace]
  refine ⟨46598702577397431888328393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62131603436529909184437857 46598702577397431888328393)
  ·
    refine ⟨34949026933048073916246295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46598702577397431888328393 34949026933048073916246295)
    ·
      refine ⟨52423540399572110874369443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34949026933048073916246295 52423540399572110874369443)
      ·
        refine ⟨78635310599358166311554165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52423540399572110874369443 78635310599358166311554165)
        ·
          refine ⟨7372060368689828091708203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78635310599358166311554165 7372060368689828091708203)
          ·
            refine ⟨11058090553034742137562305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7372060368689828091708203 11058090553034742137562305)
            ·
              refine ⟨8293567914776056603171729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11058090553034742137562305 8293567914776056603171729)
              ·
                refine ⟨6220175936082042452378797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8293567914776056603171729 6220175936082042452378797)
                ·
                  refine ⟨2332565976030765919642049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6220175936082042452378797 2332565976030765919642049)
                  ·
                    refine ⟨1749424482023074439731537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2332565976030765919642049 1749424482023074439731537)
                    ·
                      refine ⟨1312068361517305829798653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1749424482023074439731537 1312068361517305829798653)
                      ·
                        rfl

theorem cell23_2555244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 2, 2].length) (baseStart_2555244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555244 prefixEnd_2555244 := by exact prefixLift 2555244
  have htrace : WordTrace (prefixWord ++ tailWord_2555244) baseStart_2555244 baseEnd_2555244 := by
    simpa [prefixWord, tailWord_2555244, baseEnd_2555244] using wordTrace_append hprefix tailTrace_2555244
  have hstable : (prefixWord ++ tailWord_2555244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555244).length < 2 ^ (prefixWord ++ tailWord_2555244).sum := by decide
  have hdescent : baseEnd_2555244 < baseStart_2555244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555247 : List Nat := [1, 1, 2, 1, 3, 1, 6, 2, 1, 2, 3]
def baseStart_2555247 : Nat := 118140960795 + 2555247 * 2 ^ 59
def prefixEnd_2555247 : Nat := 4983230072969 + 3 ^ 40 * 2555247 * 2
def baseEnd_2555247 : Nat := 1312069901959269318061139

theorem tailTrace_2555247 : CollatzResearch.WordTrace tailWord_2555247 prefixEnd_2555247 1312069901959269318061139 := by
  unfold tailWord_2555247
  simp only [CollatzResearch.WordTrace]
  refine ⟨93197514573783995289015995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62131676382522663526010663 93197514573783995289015995)
  ·
    refine ⟨139796271860675992933523993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93197514573783995289015995 139796271860675992933523993)
    ·
      refine ⟨104847203895506994700142995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139796271860675992933523993 104847203895506994700142995)
      ·
        refine ⟨157270805843260492050214493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104847203895506994700142995 157270805843260492050214493)
        ·
          refine ⟨58976552191222684518830435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157270805843260492050214493 58976552191222684518830435)
          ·
            refine ⟨88464828286834026778245653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58976552191222684518830435 88464828286834026778245653)
            ·
              refine ⟨4146788825945345005230265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 88464828286834026778245653 4146788825945345005230265)
              ·
                refine ⟨3110091619459008753922699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4146788825945345005230265 3110091619459008753922699)
                ·
                  refine ⟨4665137429188513130884049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3110091619459008753922699 4665137429188513130884049)
                  ·
                    refine ⟨3498853071891384848163037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4665137429188513130884049 3498853071891384848163037)
                    ·
                      refine ⟨1312069901959269318061139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3498853071891384848163037 1312069901959269318061139)
                      ·
                        rfl

theorem cell23_2555247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 2, 3].length) (baseStart_2555247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555247 prefixEnd_2555247 := by exact prefixLift 2555247
  have htrace : WordTrace (prefixWord ++ tailWord_2555247) baseStart_2555247 baseEnd_2555247 := by
    simpa [prefixWord, tailWord_2555247, baseEnd_2555247] using wordTrace_append hprefix tailTrace_2555247
  have hstable : (prefixWord ++ tailWord_2555247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555247).length < 2 ^ (prefixWord ++ tailWord_2555247).sum := by decide
  have hdescent : baseEnd_2555247 < baseStart_2555247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555260 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 3, 3, 3]
def baseStart_2555260 : Nat := 118140960795 + 2555260 * 2 ^ 59
def prefixEnd_2555260 : Nat := 4983230072969 + 3 ^ 40 * 2555260 * 2
def baseEnd_2555260 : Nat := 1312076577207777767198579

theorem tailTrace_2555260 : CollatzResearch.WordTrace tailWord_2555260 prefixEnd_2555260 1312076577207777767198579 := by
  unfold tailWord_2555260
  simp only [CollatzResearch.WordTrace]
  refine ⟨46598994361368449254619617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62131992481824599006159489 46598994361368449254619617)
  ·
    refine ⟨34949245771026336940964713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46598994361368449254619617 34949245771026336940964713)
    ·
      refine ⟨26211934328269752705723535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34949245771026336940964713 26211934328269752705723535)
      ·
        refine ⟨39317901492404629058585303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26211934328269752705723535 39317901492404629058585303)
        ·
          refine ⟨58976852238606943587877955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39317901492404629058585303 58976852238606943587877955)
          ·
            refine ⟨88465278357910415381816933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58976852238606943587877955 88465278357910415381816933)
            ·
              refine ⟨16587239692108202884090675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88465278357910415381816933 16587239692108202884090675)
              ·
                refine ⟨24880859538162304326136013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16587239692108202884090675 24880859538162304326136013)
                ·
                  refine ⟨9330322326810864122301005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24880859538162304326136013 9330322326810864122301005)
                  ·
                    refine ⟨3498870872554074045862877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9330322326810864122301005 3498870872554074045862877)
                    ·
                      refine ⟨1312076577207777767198579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3498870872554074045862877 1312076577207777767198579)
                      ·
                        rfl

theorem cell23_2555260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_2555260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555260 prefixEnd_2555260 := by exact prefixLift 2555260
  have htrace : WordTrace (prefixWord ++ tailWord_2555260) baseStart_2555260 baseEnd_2555260 := by
    simpa [prefixWord, tailWord_2555260, baseEnd_2555260] using wordTrace_append hprefix tailTrace_2555260
  have hstable : (prefixWord ++ tailWord_2555260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555260).length < 2 ^ (prefixWord ++ tailWord_2555260).sum := by decide
  have hdescent : baseEnd_2555260 < baseStart_2555260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555278 : List Nat := [4, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2]
def baseStart_2555278 : Nat := 118140960795 + 2555278 * 2 ^ 59
def prefixEnd_2555278 : Nat := 4983230072969 + 3 ^ 40 * 2555278 * 2
def baseEnd_2555278 : Nat := 1312085819859558696773497

theorem tailTrace_2555278 : CollatzResearch.WordTrace tailWord_2555278 prefixEnd_2555278 1312085819859558696773497 := by
  unfold tailWord_2555278
  simp only [CollatzResearch.WordTrace]
  refine ⟨11649830654583960947924311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62132430157781125055596325 11649830654583960947924311)
  ·
    refine ⟨17474745981875941421886467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11649830654583960947924311 17474745981875941421886467)
    ·
      refine ⟨26212118972813912132829701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17474745981875941421886467 26212118972813912132829701)
      ·
        refine ⟨4914772307402608524905569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26212118972813912132829701 4914772307402608524905569)
        ·
          refine ⟨3686079230551956393679177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4914772307402608524905569 3686079230551956393679177)
          ·
            refine ⟨2764559422913967295259383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3686079230551956393679177 2764559422913967295259383)
            ·
              refine ⟨4146839134370950942889075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2764559422913967295259383 4146839134370950942889075)
              ·
                refine ⟨6220258701556426414333613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4146839134370950942889075 6220258701556426414333613)
                ·
                  refine ⟨2332597013083659905375105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6220258701556426414333613 2332597013083659905375105)
                  ·
                    refine ⟨1749447759812744929031329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2332597013083659905375105 1749447759812744929031329)
                    ·
                      refine ⟨1312085819859558696773497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1749447759812744929031329 1312085819859558696773497)
                      ·
                        rfl

theorem cell23_2555278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_2555278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555278 prefixEnd_2555278 := by exact prefixLift 2555278
  have htrace : WordTrace (prefixWord ++ tailWord_2555278) baseStart_2555278 baseEnd_2555278 := by
    simpa [prefixWord, tailWord_2555278, baseEnd_2555278] using wordTrace_append hprefix tailTrace_2555278
  have hstable : (prefixWord ++ tailWord_2555278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555278).length < 2 ^ (prefixWord ++ tailWord_2555278).sum := by decide
  have hdescent : baseEnd_2555278 < baseStart_2555278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555287 : List Nat := [1, 1, 3, 3, 1, 1, 1, 4, 3, 3, 2]
def baseStart_2555287 : Nat := 118140960795 + 2555287 * 2 ^ 59
def prefixEnd_2555287 : Nat := 4983230072969 + 3 ^ 40 * 2555287 * 2
def baseEnd_2555287 : Nat := 1312090441185449161560955

theorem tailTrace_2555287 : CollatzResearch.WordTrace tailWord_2555287 prefixEnd_2555287 1312090441185449161560955 := by
  unfold tailWord_2555287
  simp only [CollatzResearch.WordTrace]
  refine ⟨93198973493639082120472115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62132648995759388080314743 93198973493639082120472115)
  ·
    refine ⟨139798460240458623180708173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93198973493639082120472115 139798460240458623180708173)
    ·
      refine ⟨52424422590171983692765565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139798460240458623180708173 52424422590171983692765565)
      ·
        refine ⟨19659158471314493884787087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52424422590171983692765565 19659158471314493884787087)
        ·
          refine ⟨29488737706971740827180631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19659158471314493884787087 29488737706971740827180631)
          ·
            refine ⟨44233106560457611240770947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29488737706971740827180631 44233106560457611240770947)
            ·
              refine ⟨66349659840686416861156421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44233106560457611240770947 66349659840686416861156421)
              ·
                refine ⟨12440561220128703161466829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66349659840686416861156421 12440561220128703161466829)
                ·
                  refine ⟨4665210457548263685550061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12440561220128703161466829 4665210457548263685550061)
                  ·
                    refine ⟨1749453921580598882081273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4665210457548263685550061 1749453921580598882081273)
                    ·
                      refine ⟨1312090441185449161560955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1749453921580598882081273 1312090441185449161560955)
                      ·
                        rfl

theorem cell23_2555287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_2555287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555287 prefixEnd_2555287 := by exact prefixLift 2555287
  have htrace : WordTrace (prefixWord ++ tailWord_2555287) baseStart_2555287 baseEnd_2555287 := by
    simpa [prefixWord, tailWord_2555287, baseEnd_2555287] using wordTrace_append hprefix tailTrace_2555287
  have hstable : (prefixWord ++ tailWord_2555287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555287).length < 2 ^ (prefixWord ++ tailWord_2555287).sum := by decide
  have hdescent : baseEnd_2555287 < baseStart_2555287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555288 : List Nat := [2, 1, 2, 5, 3, 1, 2, 1, 2, 4]
def baseStart_2555288 : Nat := 118140960795 + 2555288 * 2 ^ 59
def prefixEnd_2555288 : Nat := 4983230072969 + 3 ^ 40 * 2555288 * 2
def baseEnd_2555288 : Nat := 437363651555367885882817

theorem tailTrace_2555288 : CollatzResearch.WordTrace tailWord_2555288 prefixEnd_2555288 437363651555367885882817 := by
  unfold tailWord_2555288
  simp only [CollatzResearch.WordTrace]
  refine ⟨46599504983317729645629259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62132673311090306194172345 46599504983317729645629259)
  ·
    refine ⟨69899257474976594468443889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46599504983317729645629259 69899257474976594468443889)
    ·
      refine ⟨52424443106232445851332917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69899257474976594468443889 52424443106232445851332917)
      ·
        refine ⟨4914791541209291798562461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52424443106232445851332917 4914791541209291798562461)
        ·
          refine ⟨1843046827953484424460923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4914791541209291798562461 1843046827953484424460923)
          ·
            refine ⟨2764570241930226636691385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1843046827953484424460923 2764570241930226636691385)
            ·
              refine ⟨2073427681447669977518539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2764570241930226636691385 2073427681447669977518539)
              ·
                refine ⟨3110141522171504966277809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2073427681447669977518539 3110141522171504966277809)
                ·
                  refine ⟨2332606141628628724708357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3110141522171504966277809 2332606141628628724708357)
                  ·
                    refine ⟨437363651555367885882817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2332606141628628724708357 437363651555367885882817)
                    ·
                      rfl

theorem cell23_2555288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 2, 4].length) (baseStart_2555288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555288 prefixEnd_2555288 := by exact prefixLift 2555288
  have htrace : WordTrace (prefixWord ++ tailWord_2555288) baseStart_2555288 baseEnd_2555288 := by
    simpa [prefixWord, tailWord_2555288, baseEnd_2555288] using wordTrace_append hprefix tailTrace_2555288
  have hstable : (prefixWord ++ tailWord_2555288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555288).length < 2 ^ (prefixWord ++ tailWord_2555288).sum := by decide
  have hdescent : baseEnd_2555288 < baseStart_2555288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555320 : List Nat := [2, 1, 2, 1, 2, 2, 4, 1, 2, 1, 5]
def baseStart_2555320 : Nat := 118140960795 + 2555320 * 2 ^ 59
def prefixEnd_2555320 : Nat := 4983230072969 + 3 ^ 40 * 2555320 * 2
def baseEnd_2555320 : Nat := 1312107386047047532448303

theorem tailTrace_2555320 : CollatzResearch.WordTrace tailWord_2555320 prefixEnd_2555320 1312107386047047532448303 := by
  unfold tailWord_2555320
  simp only [CollatzResearch.WordTrace]
  refine ⟨46600088551259764378211707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62133451401679685837615609 46600088551259764378211707)
  ·
    refine ⟨69900132826889646567317561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46600088551259764378211707 69900132826889646567317561)
    ·
      refine ⟨52425099620167234925488171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69900132826889646567317561 52425099620167234925488171)
      ·
        refine ⟨78637649430250852388232257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52425099620167234925488171 78637649430250852388232257)
        ·
          refine ⟨58978237072688139291174193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78637649430250852388232257 58978237072688139291174193)
          ·
            refine ⟨44233677804516104468380645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58978237072688139291174193 44233677804516104468380645)
            ·
              refine ⟨8293814588346769587821371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44233677804516104468380645 8293814588346769587821371)
              ·
                refine ⟨12440721882520154381732057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8293814588346769587821371 12440721882520154381732057)
                ·
                  refine ⟨9330541411890115786299043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12440721882520154381732057 9330541411890115786299043)
                  ·
                    refine ⟨13995812117835173679448565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9330541411890115786299043 13995812117835173679448565)
                    ·
                      refine ⟨1312107386047047532448303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13995812117835173679448565 1312107386047047532448303)
                      ·
                        rfl

theorem cell23_2555320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_2555320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555320 prefixEnd_2555320 := by exact prefixLift 2555320
  have htrace : WordTrace (prefixWord ++ tailWord_2555320) baseStart_2555320 baseEnd_2555320 := by
    simpa [prefixWord, tailWord_2555320, baseEnd_2555320] using wordTrace_append hprefix tailTrace_2555320
  have hstable : (prefixWord ++ tailWord_2555320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555320).length < 2 ^ (prefixWord ++ tailWord_2555320).sum := by decide
  have hdescent : baseEnd_2555320 < baseStart_2555320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555357 : List Nat := [1, 4, 3, 1, 1, 3, 1, 2, 7]
def baseStart_2555357 : Nat := 118140960795 + 2555357 * 2 ^ 59
def prefixEnd_2555357 : Nat := 4983230072969 + 3 ^ 40 * 2555357 * 2
def baseEnd_2555357 : Nat := 145791820536807098631737

theorem tailTrace_2555357 : CollatzResearch.WordTrace tailWord_2555357 prefixEnd_2555357 145791820536807098631737 := by
  unfold tailWord_2555357
  simp only [CollatzResearch.WordTrace]
  refine ⟨93201526603385484075520325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62134351068923656050346883 93201526603385484075520325)
  ·
    refine ⟨17475286238134778264160061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93201526603385484075520325 17475286238134778264160061)
    ·
      refine ⟨6553232339300541849060023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17475286238134778264160061 6553232339300541849060023)
      ·
        refine ⟨9829848508950812773590035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6553232339300541849060023 9829848508950812773590035)
        ·
          refine ⟨14744772763426219160385053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9829848508950812773590035 14744772763426219160385053)
          ·
            refine ⟨5529289786284832185144395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14744772763426219160385053 5529289786284832185144395)
            ·
              refine ⟨8293934679427248277716593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5529289786284832185144395 8293934679427248277716593)
              ·
                refine ⟨6220451009570436208287445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8293934679427248277716593 6220451009570436208287445)
                ·
                  refine ⟨145791820536807098631737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6220451009570436208287445 145791820536807098631737)
                  ·
                    rfl

theorem cell23_2555357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 7].length) (baseStart_2555357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555357 prefixEnd_2555357 := by exact prefixLift 2555357
  have htrace : WordTrace (prefixWord ++ tailWord_2555357) baseStart_2555357 baseEnd_2555357 := by
    simpa [prefixWord, tailWord_2555357, baseEnd_2555357] using wordTrace_append hprefix tailTrace_2555357
  have hstable : (prefixWord ++ tailWord_2555357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555357).length < 2 ^ (prefixWord ++ tailWord_2555357).sum := by decide
  have hdescent : baseEnd_2555357 < baseStart_2555357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555374 : List Nat := [4, 1, 2, 1, 2, 1, 4, 3, 5]
def baseStart_2555374 : Nat := 118140960795 + 2555374 * 2 ^ 59
def prefixEnd_2555374 : Nat := 4983230072969 + 3 ^ 40 * 2555374 * 2
def baseEnd_2555374 : Nat := 145792790444710035685895

theorem tailTrace_2555374 : CollatzResearch.WordTrace tailWord_2555374 prefixEnd_2555374 145792790444710035685895 := by
  unfold tailWord_2555374
  simp only [CollatzResearch.WordTrace]
  refine ⟨11650268330540486997361147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62134764429549263985926117 11650268330540486997361147)
  ·
    refine ⟨17475402495810730496041721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11650268330540486997361147 17475402495810730496041721)
    ·
      refine ⟨13106551871858047872031291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17475402495810730496041721 13106551871858047872031291)
      ·
        refine ⟨19659827807787071808046937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13106551871858047872031291 19659827807787071808046937)
        ·
          refine ⟨14744870855840303856035203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19659827807787071808046937 14744870855840303856035203)
          ·
            refine ⟨22117306283760455784052805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14744870855840303856035203 22117306283760455784052805)
            ·
              refine ⟨4146994928205085459509901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22117306283760455784052805 4146994928205085459509901)
              ·
                refine ⟨1555123098076907047316213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4146994928205085459509901 1555123098076907047316213)
                ·
                  refine ⟨145792790444710035685895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1555123098076907047316213 145792790444710035685895)
                  ·
                    rfl

theorem cell23_2555374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3, 5].length) (baseStart_2555374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555374 prefixEnd_2555374 := by exact prefixLift 2555374
  have htrace : WordTrace (prefixWord ++ tailWord_2555374) baseStart_2555374 baseEnd_2555374 := by
    simpa [prefixWord, tailWord_2555374, baseEnd_2555374] using wordTrace_append hprefix tailTrace_2555374
  have hstable : (prefixWord ++ tailWord_2555374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555374).length < 2 ^ (prefixWord ++ tailWord_2555374).sum := by decide
  have hdescent : baseEnd_2555374 < baseStart_2555374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555407 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 6, 4, 2]
def baseStart_2555407 : Nat := 118140960795 + 2555407 * 2 ^ 59
def prefixEnd_2555407 : Nat := 4983230072969 + 3 ^ 40 * 2555407 * 2
def baseEnd_2555407 : Nat := 1312152058863988692060403

theorem tailTrace_2555407 : CollatzResearch.WordTrace tailWord_2555407 prefixEnd_2555407 1312152058863988692060403 := by
  unfold tailWord_2555407
  simp only [CollatzResearch.WordTrace]
  refine ⟨93203350253204342614840475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62135566835469561743226983 93203350253204342614840475)
  ·
    refine ⟨139805025379806513922260713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93203350253204342614840475 139805025379806513922260713)
    ·
      refine ⟨104853769034854885441695535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139805025379806513922260713 104853769034854885441695535)
      ·
        refine ⟨157280653552282328162543303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104853769034854885441695535 157280653552282328162543303)
        ·
          refine ⟨235920980328423492243814955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157280653552282328162543303 235920980328423492243814955)
          ·
            refine ⟨353881470492635238365722433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235920980328423492243814955 353881470492635238365722433)
            ·
              refine ⟨265411102869476428774291825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 353881470492635238365722433 265411102869476428774291825)
              ·
                refine ⟨199058327152107321580718869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 265411102869476428774291825 199058327152107321580718869)
                ·
                  refine ⟨9330859085255030699096197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 199058327152107321580718869 9330859085255030699096197)
                  ·
                    refine ⟨1749536078485318256080537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9330859085255030699096197 1749536078485318256080537)
                    ·
                      refine ⟨1312152058863988692060403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1749536078485318256080537 1312152058863988692060403)
                      ·
                        rfl

theorem cell23_2555407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 4, 2].length) (baseStart_2555407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555407 prefixEnd_2555407 := by exact prefixLift 2555407
  have htrace : WordTrace (prefixWord ++ tailWord_2555407) baseStart_2555407 baseEnd_2555407 := by
    simpa [prefixWord, tailWord_2555407, baseEnd_2555407] using wordTrace_append hprefix tailTrace_2555407
  have hstable : (prefixWord ++ tailWord_2555407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555407).length < 2 ^ (prefixWord ++ tailWord_2555407).sum := by decide
  have hdescent : baseEnd_2555407 < baseStart_2555407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555502 : List Nat := [4, 1, 2, 2, 4, 1, 2, 2, 1, 4]
def baseStart_2555502 : Nat := 118140960795 + 2555502 * 2 ^ 59
def prefixEnd_2555502 : Nat := 4983230072969 + 3 ^ 40 * 2555502 * 2
def baseEnd_2555502 : Nat := 437400279842055273457489

theorem tailTrace_2555502 : CollatzResearch.WordTrace tailWord_2555502 prefixEnd_2555502 437400279842055273457489 := by
  unfold tailWord_2555502
  simp only [CollatzResearch.WordTrace]
  refine ⟨11650851898482521729943595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62137876791906782559699173 11650851898482521729943595)
  ·
    refine ⟨17476277847723782594915393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11650851898482521729943595 17476277847723782594915393)
    ·
      refine ⟨13107208385792836946186545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17476277847723782594915393 13107208385792836946186545)
      ·
        refine ⟨9830406289344627709639909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13107208385792836946186545 9830406289344627709639909)
        ·
          refine ⟨1843201179252117695557483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9830406289344627709639909 1843201179252117695557483)
          ·
            refine ⟨2764801768878176543336225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1843201179252117695557483 2764801768878176543336225)
            ·
              refine ⟨2073601326658632407502169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2764801768878176543336225 2073601326658632407502169)
              ·
                refine ⟨1555200994993974305626627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2073601326658632407502169 1555200994993974305626627)
                ·
                  refine ⟨2332801492490961458439941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1555200994993974305626627 2332801492490961458439941)
                  ·
                    refine ⟨437400279842055273457489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2332801492490961458439941 437400279842055273457489)
                    ·
                      rfl

theorem cell23_2555502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_2555502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555502 prefixEnd_2555502 := by exact prefixLift 2555502
  have htrace : WordTrace (prefixWord ++ tailWord_2555502) baseStart_2555502 baseEnd_2555502 := by
    simpa [prefixWord, tailWord_2555502, baseEnd_2555502] using wordTrace_append hprefix tailTrace_2555502
  have hstable : (prefixWord ++ tailWord_2555502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555502).length < 2 ^ (prefixWord ++ tailWord_2555502).sum := by decide
  have hdescent : baseEnd_2555502 < baseStart_2555502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555507 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 8, 4]
def baseStart_2555507 : Nat := 118140960795 + 2555507 * 2 ^ 59
def prefixEnd_2555507 : Nat := 4983230072969 + 3 ^ 40 * 2555507 * 2
def baseEnd_2555507 : Nat := 437401135643146100269981

theorem tailTrace_2555507 : CollatzResearch.WordTrace tailWord_2555507 prefixEnd_2555507 437401135643146100269981 := by
  unfold tailWord_2555507
  simp only [CollatzResearch.WordTrace]
  refine ⟨93206997552842059693480775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62137998368561373128987183 93206997552842059693480775)
  ·
    refine ⟨139810496329263089540221163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93206997552842059693480775 139810496329263089540221163)
    ·
      refine ⟨209715744493894634310331745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139810496329263089540221163 209715744493894634310331745)
      ·
        refine ⟨157286808370420975732748809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209715744493894634310331745 157286808370420975732748809)
        ·
          refine ⟨117965106277815731799561607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157286808370420975732748809 117965106277815731799561607)
          ·
            refine ⟨176947659416723597699342411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117965106277815731799561607 176947659416723597699342411)
            ·
              refine ⟨265421489125085396549013617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176947659416723597699342411 265421489125085396549013617)
              ·
                refine ⟨199066116843814047411760213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 265421489125085396549013617 199066116843814047411760213)
                ·
                  refine ⟨2332806056763445868106565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 199066116843814047411760213 2332806056763445868106565)
                  ·
                    refine ⟨437401135643146100269981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2332806056763445868106565 437401135643146100269981)
                    ·
                      rfl

theorem cell23_2555507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8, 4].length) (baseStart_2555507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555507 prefixEnd_2555507 := by exact prefixLift 2555507
  have htrace : WordTrace (prefixWord ++ tailWord_2555507) baseStart_2555507 baseEnd_2555507 := by
    simpa [prefixWord, tailWord_2555507, baseEnd_2555507] using wordTrace_append hprefix tailTrace_2555507
  have hstable : (prefixWord ++ tailWord_2555507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555507).length < 2 ^ (prefixWord ++ tailWord_2555507).sum := by decide
  have hdescent : baseEnd_2555507 < baseStart_2555507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555531 : List Nat := [1, 1, 1, 1, 4, 1, 5, 2, 3, 2, 2]
def baseStart_2555531 : Nat := 118140960795 + 2555531 * 2 ^ 59
def prefixEnd_2555531 : Nat := 4983230072969 + 3 ^ 40 * 2555531 * 2
def baseEnd_2555531 : Nat := 1312215730465146206909833

theorem tailTrace_2555531 : CollatzResearch.WordTrace tailWord_2555531 prefixEnd_2555531 1312215730465146206909833 := by
  unfold tailWord_2555531
  simp only [CollatzResearch.WordTrace]
  refine ⟨93207872904755111792354447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62138581936503407861569631 93207872904755111792354447)
  ·
    refine ⟨139811809357132667688531671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93207872904755111792354447 139811809357132667688531671)
    ·
      refine ⟨209717714035699001532797507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139811809357132667688531671 209717714035699001532797507)
      ·
        refine ⟨314576571053548502299196261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209717714035699001532797507 314576571053548502299196261)
        ·
          refine ⟨58983107072540344181099299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 314576571053548502299196261 58983107072540344181099299)
          ·
            refine ⟨88474660608810516271648949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58983107072540344181099299 88474660608810516271648949)
            ·
              refine ⟨8294499432075985900467089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88474660608810516271648949 8294499432075985900467089)
              ·
                refine ⟨6220874574056989425350317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8294499432075985900467089 6220874574056989425350317)
                ·
                  refine ⟨2332827965271371034506369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6220874574056989425350317 2332827965271371034506369)
                  ·
                    refine ⟨1749620973953528275879777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2332827965271371034506369 1749620973953528275879777)
                    ·
                      refine ⟨1312215730465146206909833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1749620973953528275879777 1312215730465146206909833)
                      ·
                        rfl

theorem cell23_2555531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3, 2, 2].length) (baseStart_2555531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555531 prefixEnd_2555531 := by exact prefixLift 2555531
  have htrace : WordTrace (prefixWord ++ tailWord_2555531) baseStart_2555531 baseEnd_2555531 := by
    simpa [prefixWord, tailWord_2555531, baseEnd_2555531] using wordTrace_append hprefix tailTrace_2555531
  have hstable : (prefixWord ++ tailWord_2555531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555531).length < 2 ^ (prefixWord ++ tailWord_2555531).sum := by decide
  have hdescent : baseEnd_2555531 < baseStart_2555531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555544 : List Nat := [2, 1, 2, 4, 1, 2, 2, 2, 1, 2, 4]
def baseStart_2555544 : Nat := 118140960795 + 2555544 * 2 ^ 59
def prefixEnd_2555544 : Nat := 4983230072969 + 3 ^ 40 * 2555544 * 2
def baseEnd_2555544 : Nat := 1312222405713654656047273

theorem tailTrace_2555544 : CollatzResearch.WordTrace tailWord_2555544 prefixEnd_2555544 1312222405713654656047273 := by
  unfold tailWord_2555544
  simp only [CollatzResearch.WordTrace]
  refine ⟨46604173526854007506288843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62138898035805343341718457 46604173526854007506288843)
  ·
    refine ⟨69906260290281011259433265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46604173526854007506288843 69906260290281011259433265)
    ·
      refine ⟨52429695217710758444574949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69906260290281011259433265 52429695217710758444574949)
      ·
        refine ⟨9830567853320767208357803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52429695217710758444574949 9830567853320767208357803)
        ·
          refine ⟨14745851779981150812536705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9830567853320767208357803 14745851779981150812536705)
          ·
            refine ⟨11059388834985863109402529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14745851779981150812536705 11059388834985863109402529)
            ·
              refine ⟨8294541626239397332051897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11059388834985863109402529 8294541626239397332051897)
              ·
                refine ⟨6220906219679547999038923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8294541626239397332051897 6220906219679547999038923)
                ·
                  refine ⟨9331359329519321998558385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6220906219679547999038923 9331359329519321998558385)
                  ·
                    refine ⟨6998519497139491498918789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9331359329519321998558385 6998519497139491498918789)
                    ·
                      refine ⟨1312222405713654656047273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6998519497139491498918789 1312222405713654656047273)
                      ·
                        rfl

theorem cell23_2555544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_2555544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555544 prefixEnd_2555544 := by exact prefixLift 2555544
  have htrace : WordTrace (prefixWord ++ tailWord_2555544) baseStart_2555544 baseEnd_2555544 := by
    simpa [prefixWord, tailWord_2555544, baseEnd_2555544] using wordTrace_append hprefix tailTrace_2555544
  have hstable : (prefixWord ++ tailWord_2555544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555544).length < 2 ^ (prefixWord ++ tailWord_2555544).sum := by decide
  have hdescent : baseEnd_2555544 < baseStart_2555544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555565 : List Nat := [1, 5, 2, 1, 1, 1, 1, 6, 1, 2, 2]
def baseStart_2555565 : Nat := 118140960795 + 2555565 * 2 ^ 59
def prefixEnd_2555565 : Nat := 4983230072969 + 3 ^ 40 * 2555565 * 2
def baseEnd_2555565 : Nat := 1312233188807399073884677

theorem tailTrace_2555565 : CollatzResearch.WordTrace tailWord_2555565 prefixEnd_2555565 1312233188807399073884677 := by
  unfold tailWord_2555565
  simp only [CollatzResearch.WordTrace]
  refine ⟨93209112986631935599092149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62139408657754623732728099 93209112986631935599092149)
  ·
    refine ⟨8738354342496743962414889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93209112986631935599092149 8738354342496743962414889)
    ·
      refine ⟨6553765756872557971811167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8738354342496743962414889 6553765756872557971811167)
      ·
        refine ⟨9830648635308836957716751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6553765756872557971811167 9830648635308836957716751)
        ·
          refine ⟨14745972952963255436575127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9830648635308836957716751 14745972952963255436575127)
          ·
            refine ⟨22118959429444883154862691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14745972952963255436575127 22118959429444883154862691)
            ·
              refine ⟨33178439144167324732294037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22118959429444883154862691 33178439144167324732294037)
              ·
                refine ⟨1555239334882843346826283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33178439144167324732294037 1555239334882843346826283)
                ·
                  refine ⟨2332859002324265020239425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1555239334882843346826283 2332859002324265020239425)
                  ·
                    refine ⟨1749644251743198765179569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2332859002324265020239425 1749644251743198765179569)
                    ·
                      refine ⟨1312233188807399073884677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1749644251743198765179569 1312233188807399073884677)
                      ·
                        rfl

theorem cell23_2555565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_2555565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555565 prefixEnd_2555565 := by exact prefixLift 2555565
  have htrace : WordTrace (prefixWord ++ tailWord_2555565) baseStart_2555565 baseEnd_2555565 := by
    simpa [prefixWord, tailWord_2555565, baseEnd_2555565] using wordTrace_append hprefix tailTrace_2555565
  have hstable : (prefixWord ++ tailWord_2555565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555565).length < 2 ^ (prefixWord ++ tailWord_2555565).sum := by decide
  have hdescent : baseEnd_2555565 < baseStart_2555565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555634 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 1, 4, 4]
def baseStart_2555634 : Nat := 118140960795 + 2555634 * 2 ^ 59
def prefixEnd_2555634 : Nat := 4983230072969 + 3 ^ 40 * 2555634 * 2
def baseEnd_2555634 : Nat := 1312268618972559303921859

theorem tailTrace_2555634 : CollatzResearch.WordTrace tailWord_2555634 prefixEnd_2555634 1312268618972559303921859 := by
  unfold tailWord_2555634
  simp only [CollatzResearch.WordTrace]
  refine ⟨23302907405845490095838489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62141086415587973588902637 23302907405845490095838489)
  ·
    refine ⟨17477180554384117571878867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23302907405845490095838489 17477180554384117571878867)
    ·
      refine ⟨26215770831576176357818301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17477180554384117571878867 26215770831576176357818301)
      ·
        refine ⟨9830914061841066134181863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26215770831576176357818301 9830914061841066134181863)
        ·
          refine ⟨14746371092761599201272795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9830914061841066134181863 14746371092761599201272795)
          ·
            refine ⟨22119556639142398801909193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14746371092761599201272795 22119556639142398801909193)
            ·
              refine ⟨16589667479356799101431895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22119556639142398801909193 16589667479356799101431895)
              ·
                refine ⟨24884501219035198652147843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16589667479356799101431895 24884501219035198652147843)
                ·
                  refine ⟨37326751828552797978221765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24884501219035198652147843 37326751828552797978221765)
                  ·
                    refine ⟨6998765967853649620916581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37326751828552797978221765 6998765967853649620916581)
                    ·
                      refine ⟨1312268618972559303921859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6998765967853649620916581 1312268618972559303921859)
                      ·
                        rfl

theorem cell23_2555634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_2555634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555634 prefixEnd_2555634 := by exact prefixLift 2555634
  have htrace : WordTrace (prefixWord ++ tailWord_2555634) baseStart_2555634 baseEnd_2555634 := by
    simpa [prefixWord, tailWord_2555634, baseEnd_2555634] using wordTrace_append hprefix tailTrace_2555634
  have hstable : (prefixWord ++ tailWord_2555634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555634).length < 2 ^ (prefixWord ++ tailWord_2555634).sum := by decide
  have hdescent : baseEnd_2555634 < baseStart_2555634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555681 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 2, 5, 2]
def baseStart_2555681 : Nat := 118140960795 + 2555681 * 2 ^ 59
def prefixEnd_2555681 : Nat := 4983230072969 + 3 ^ 40 * 2555681 * 2
def baseEnd_2555681 : Nat := 1312292752563320620034143

theorem tailTrace_2555681 : CollatzResearch.WordTrace tailWord_2555681 prefixEnd_2555681 1312292752563320620034143 := by
  unfold tailWord_2555681
  simp only [CollatzResearch.WordTrace]
  refine ⟨93213343854211687410314897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62142229236141124940209931 93213343854211687410314897)
  ·
    refine ⟨69910007890658765557736173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93213343854211687410314897 69910007890658765557736173)
    ·
      refine ⟨26216252958997037084151065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69910007890658765557736173 26216252958997037084151065)
      ·
        refine ⟨19662189719247777813113299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26216252958997037084151065 19662189719247777813113299)
        ·
          refine ⟨29493284578871666719669949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19662189719247777813113299 29493284578871666719669949)
          ·
            refine ⟨11059981717076875019876231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29493284578871666719669949 11059981717076875019876231)
            ·
              refine ⟨16589972575615312529814347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11059981717076875019876231 16589972575615312529814347)
              ·
                refine ⟨24884958863422968794721521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16589972575615312529814347 24884958863422968794721521)
                ·
                  refine ⟨18663719147567226596041141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24884958863422968794721521 18663719147567226596041141)
                  ·
                    refine ⟨1749723670084427493378857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18663719147567226596041141 1749723670084427493378857)
                    ·
                      refine ⟨1312292752563320620034143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1749723670084427493378857 1312292752563320620034143)
                      ·
                        rfl

theorem cell23_2555681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_2555681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555681 prefixEnd_2555681 := by exact prefixLift 2555681
  have htrace : WordTrace (prefixWord ++ tailWord_2555681) baseStart_2555681 baseEnd_2555681 := by
    simpa [prefixWord, tailWord_2555681, baseEnd_2555681] using wordTrace_append hprefix tailTrace_2555681
  have hstable : (prefixWord ++ tailWord_2555681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555681).length < 2 ^ (prefixWord ++ tailWord_2555681).sum := by decide
  have hdescent : baseEnd_2555681 < baseStart_2555681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555711 : List Nat := [1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 4]
def baseStart_2555711 : Nat := 118140960795 + 2555711 * 2 ^ 59
def prefixEnd_2555711 : Nat := 4983230072969 + 3 ^ 40 * 2555711 * 2
def baseEnd_2555711 : Nat := 1312308156982955502659005

theorem tailTrace_2555711 : CollatzResearch.WordTrace tailWord_2555711 prefixEnd_2555711 1312308156982955502659005 := by
  unfold tailWord_2555711
  simp only [CollatzResearch.WordTrace]
  refine ⟨93214438044103002533906987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62142958696068668355937991 93214438044103002533906987)
  ·
    refine ⟨139821657066154503800860481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93214438044103002533906987 139821657066154503800860481)
    ·
      refine ⟨104866242799615877850645361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139821657066154503800860481 104866242799615877850645361)
      ·
        refine ⟨78649682099711908387984021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104866242799615877850645361 78649682099711908387984021)
        ·
          refine ⟨3686703848423995705686751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 78649682099711908387984021 3686703848423995705686751)
          ·
            refine ⟨5530055772635993558530127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3686703848423995705686751 5530055772635993558530127)
            ·
              refine ⟨8295083658953990337795191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5530055772635993558530127 8295083658953990337795191)
              ·
                refine ⟨12442625488430985506692787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8295083658953990337795191 12442625488430985506692787)
                ·
                  refine ⟨18663938232646478260039181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12442625488430985506692787 18663938232646478260039181)
                  ·
                    refine ⟨6998976837242429347514693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18663938232646478260039181 6998976837242429347514693)
                    ·
                      refine ⟨1312308156982955502659005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6998976837242429347514693 1312308156982955502659005)
                      ·
                        rfl

theorem cell23_2555711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 4].length) (baseStart_2555711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555711 prefixEnd_2555711 := by exact prefixLift 2555711
  have htrace : WordTrace (prefixWord ++ tailWord_2555711) baseStart_2555711 baseEnd_2555711 := by
    simpa [prefixWord, tailWord_2555711, baseEnd_2555711] using wordTrace_append hprefix tailTrace_2555711
  have hstable : (prefixWord ++ tailWord_2555711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555711).length < 2 ^ (prefixWord ++ tailWord_2555711).sum := by decide
  have hdescent : baseEnd_2555711 < baseStart_2555711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555738 : List Nat := [3, 1, 1, 2, 1, 3, 1, 6, 1, 4]
def baseStart_2555738 : Nat := 118140960795 + 2555738 * 2 ^ 59
def prefixEnd_2555738 : Nat := 4983230072969 + 3 ^ 40 * 2555738 * 2
def baseEnd_2555738 : Nat := 437440673653542299007127

theorem tailTrace_2555738 : CollatzResearch.WordTrace tailWord_2555738 prefixEnd_2555738 437440673653542299007127 := by
  unfold tailWord_2555738
  simp only [CollatzResearch.WordTrace]
  refine ⟨23303855703751296536284967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62143615210003457430093245 23303855703751296536284967)
  ·
    refine ⟨34955783555626944804427451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23303855703751296536284967 34955783555626944804427451)
    ·
      refine ⟨52433675333440417206641177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34955783555626944804427451 52433675333440417206641177)
      ·
        refine ⟨39325256500080312904980883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52433675333440417206641177 39325256500080312904980883)
        ·
          refine ⟨58987884750120469357471325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39325256500080312904980883 58987884750120469357471325)
          ·
            refine ⟨22120456781295176009051747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58987884750120469357471325 22120456781295176009051747)
            ·
              refine ⟨33180685171942764013577621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22120456781295176009051747 33180685171942764013577621)
              ·
                refine ⟨1555344617434817063136451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33180685171942764013577621 1555344617434817063136451)
                ·
                  refine ⟨2333016926152225594704677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1555344617434817063136451 2333016926152225594704677)
                  ·
                    refine ⟨437440673653542299007127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2333016926152225594704677 437440673653542299007127)
                    ·
                      rfl

theorem cell23_2555738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6, 1, 4].length) (baseStart_2555738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555738 prefixEnd_2555738 := by exact prefixLift 2555738
  have htrace : WordTrace (prefixWord ++ tailWord_2555738) baseStart_2555738 baseEnd_2555738 := by
    simpa [prefixWord, tailWord_2555738, baseEnd_2555738] using wordTrace_append hprefix tailTrace_2555738
  have hstable : (prefixWord ++ tailWord_2555738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555738).length < 2 ^ (prefixWord ++ tailWord_2555738).sum := by decide
  have hdescent : baseEnd_2555738 < baseStart_2555738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555781 : List Nat := [1, 3, 1, 1, 3, 2, 1, 5, 1, 5]
def baseStart_2555781 : Nat := 118140960795 + 2555781 * 2 ^ 59
def prefixEnd_2555781 : Nat := 4983230072969 + 3 ^ 40 * 2555781 * 2
def baseEnd_2555781 : Nat := 437448033542923409594561

theorem tailTrace_2555781 : CollatzResearch.WordTrace tailWord_2555781 prefixEnd_2555781 437448033542923409594561 := by
  unfold tailWord_2555781
  simp only [CollatzResearch.WordTrace]
  refine ⟨93216991153849404488955197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62144660769232936325970131 93216991153849404488955197)
  ·
    refine ⟨34956371682693526683358199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93216991153849404488955197 34956371682693526683358199)
    ·
      refine ⟨52434557524040290025037299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34956371682693526683358199 52434557524040290025037299)
      ·
        refine ⟨78651836286060435037555949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52434557524040290025037299 78651836286060435037555949)
        ·
          refine ⟨29494438607272663139083481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78651836286060435037555949 29494438607272663139083481)
          ·
            refine ⟨22120828955454497354312611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29494438607272663139083481 22120828955454497354312611)
            ·
              refine ⟨33181243433181746031468917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22120828955454497354312611 33181243433181746031468917)
              ·
                refine ⟨3110741571860788690450211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33181243433181746031468917 3110741571860788690450211)
                ·
                  refine ⟨4666112357791183035675317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3110741571860788690450211 4666112357791183035675317)
                  ·
                    refine ⟨437448033542923409594561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4666112357791183035675317 437448033542923409594561)
                    ·
                      rfl

theorem cell23_2555781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 5].length) (baseStart_2555781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555781 prefixEnd_2555781 := by exact prefixLift 2555781
  have htrace : WordTrace (prefixWord ++ tailWord_2555781) baseStart_2555781 baseEnd_2555781 := by
    simpa [prefixWord, tailWord_2555781, baseEnd_2555781] using wordTrace_append hprefix tailTrace_2555781
  have hstable : (prefixWord ++ tailWord_2555781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555781).length < 2 ^ (prefixWord ++ tailWord_2555781).sum := by decide
  have hdescent : baseEnd_2555781 < baseStart_2555781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555815 : List Nat := [1, 1, 6, 1, 2, 3, 1, 2, 1, 5]
def baseStart_2555815 : Nat := 118140960795 + 2555815 * 2 ^ 59
def prefixEnd_2555815 : Nat := 4983230072969 + 3 ^ 40 * 2555815 * 2
def baseEnd_2555815 : Nat := 437453852990341031919509

theorem tailTrace_2555815 : CollatzResearch.WordTrace tailWord_2555815 prefixEnd_2555815 437453852990341031919509 := by
  unfold tailWord_2555815
  simp only [CollatzResearch.WordTrace]
  refine ⟨93218231235726228295692899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62145487490484152197128599 93218231235726228295692899)
  ·
    refine ⟨139827346853589342443539349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93218231235726228295692899 139827346853589342443539349)
    ·
      refine ⟨6554406883762000427040907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 139827346853589342443539349 6554406883762000427040907)
      ·
        refine ⟨9831610325643000640561361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6554406883762000427040907 9831610325643000640561361)
        ·
          refine ⟨7373707744232250480421021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9831610325643000640561361 7373707744232250480421021)
          ·
            refine ⟨2765140404087093930157883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7373707744232250480421021 2765140404087093930157883)
            ·
              refine ⟨4147710606130640895236825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2765140404087093930157883 4147710606130640895236825)
              ·
                refine ⟨3110782954597980671427619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4147710606130640895236825 3110782954597980671427619)
                ·
                  refine ⟨4666174431896971007141429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3110782954597980671427619 4666174431896971007141429)
                  ·
                    refine ⟨437453852990341031919509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4666174431896971007141429 437453852990341031919509)
                    ·
                      rfl

theorem cell23_2555815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_2555815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555815 prefixEnd_2555815 := by exact prefixLift 2555815
  have htrace : WordTrace (prefixWord ++ tailWord_2555815) baseStart_2555815 baseEnd_2555815 := by
    simpa [prefixWord, tailWord_2555815, baseEnd_2555815] using wordTrace_append hprefix tailTrace_2555815
  have hstable : (prefixWord ++ tailWord_2555815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555815).length < 2 ^ (prefixWord ++ tailWord_2555815).sum := by decide
  have hdescent : baseEnd_2555815 < baseStart_2555815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555838 : List Nat := [4, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5]
def baseStart_2555838 : Nat := 118140960795 + 2555838 * 2 ^ 59
def prefixEnd_2555838 : Nat := 4983230072969 + 3 ^ 40 * 2555838 * 2
def baseEnd_2555838 : Nat := 1312373369026076505770921

theorem tailTrace_2555838 : CollatzResearch.WordTrace tailWord_2555838 prefixEnd_2555838 1312373369026076505770921 := by
  unfold tailWord_2555838
  simp only [CollatzResearch.WordTrace]
  refine ⟨11652383764330362902972521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62146046743095268815853445 11652383764330362902972521)
  ·
    refine ⟨8739287823247772177229391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11652383764330362902972521 8739287823247772177229391)
    ·
      refine ⟨13108931734871658265844087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8739287823247772177229391 13108931734871658265844087)
      ·
        refine ⟨19663397602307487398766131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13108931734871658265844087 19663397602307487398766131)
        ·
          refine ⟨29495096403461231098149197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19663397602307487398766131 29495096403461231098149197)
          ·
            refine ⟨11060661151297961661805949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29495096403461231098149197 11060661151297961661805949)
            ·
              refine ⟨4147747931736735623177231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11060661151297961661805949 4147747931736735623177231)
              ·
                refine ⟨6221621897605103434765847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4147747931736735623177231 6221621897605103434765847)
                ·
                  refine ⟨9332432846407655152148771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6221621897605103434765847 9332432846407655152148771)
                  ·
                    refine ⟨13998649269611482728223157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9332432846407655152148771 13998649269611482728223157)
                    ·
                      refine ⟨1312373369026076505770921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13998649269611482728223157 1312373369026076505770921)
                      ·
                        rfl

theorem cell23_2555838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_2555838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555838 prefixEnd_2555838 := by exact prefixLift 2555838
  have htrace : WordTrace (prefixWord ++ tailWord_2555838) baseStart_2555838 baseEnd_2555838 := by
    simpa [prefixWord, tailWord_2555838, baseEnd_2555838] using wordTrace_append hprefix tailTrace_2555838
  have hstable : (prefixWord ++ tailWord_2555838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555838).length < 2 ^ (prefixWord ++ tailWord_2555838).sum := by decide
  have hdescent : baseEnd_2555838 < baseStart_2555838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555851 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 3, 3, 3]
def baseStart_2555851 : Nat := 118140960795 + 2555851 * 2 ^ 59
def prefixEnd_2555851 : Nat := 4983230072969 + 3 ^ 40 * 2555851 * 2
def baseEnd_2555851 : Nat := 1312380044274584954908361

theorem tailTrace_2555851 : CollatzResearch.WordTrace tailWord_2555851 prefixEnd_2555851 1312380044274584954908361 := by
  unfold tailWord_2555851
  simp only [CollatzResearch.WordTrace]
  refine ⟨93219544263595806444003407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62146362842397204296002271 93219544263595806444003407)
  ·
    refine ⟨139829316395393709666005111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93219544263595806444003407 139829316395393709666005111)
    ·
      refine ⟨209743974593090564499007667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139829316395393709666005111 209743974593090564499007667)
      ·
        refine ⟨314615961889635846748511501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209743974593090564499007667 314615961889635846748511501)
        ·
          refine ⟨117980985708613442530691813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 314615961889635846748511501 117980985708613442530691813)
          ·
            refine ⟨22121434820365020474504715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117980985708613442530691813 22121434820365020474504715)
            ·
              refine ⟨33182152230547530711757073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22121434820365020474504715 33182152230547530711757073)
              ·
                refine ⟨24886614172910648033817805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33182152230547530711757073 24886614172910648033817805)
                ·
                  refine ⟨9332480314841493012681677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24886614172910648033817805 9332480314841493012681677)
                  ·
                    refine ⟨3499680118065559879755629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9332480314841493012681677 3499680118065559879755629)
                    ·
                      refine ⟨1312380044274584954908361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3499680118065559879755629 1312380044274584954908361)
                      ·
                        rfl

theorem cell23_2555851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3, 3].length) (baseStart_2555851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555851 prefixEnd_2555851 := by exact prefixLift 2555851
  have htrace : WordTrace (prefixWord ++ tailWord_2555851) baseStart_2555851 baseEnd_2555851 := by
    simpa [prefixWord, tailWord_2555851, baseEnd_2555851] using wordTrace_append hprefix tailTrace_2555851
  have hstable : (prefixWord ++ tailWord_2555851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555851).length < 2 ^ (prefixWord ++ tailWord_2555851).sum := by decide
  have hdescent : baseEnd_2555851 < baseStart_2555851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555889 : List Nat := [1, 2, 2, 2, 6, 1, 2, 1, 1, 2, 3]
def baseStart_2555889 : Nat := 118140960795 + 2555889 * 2 ^ 59
def prefixEnd_2555889 : Nat := 4983230072969 + 3 ^ 40 * 2555889 * 2
def baseEnd_2555889 : Nat := 1312399556539455806233187

theorem tailTrace_2555889 : CollatzResearch.WordTrace tailWord_2555889 prefixEnd_2555889 1312399556539455806233187 := by
  unfold tailWord_2555889
  simp only [CollatzResearch.WordTrace]
  refine ⟨93220930237458138933886721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62147286824972092622591147 93220930237458138933886721)
  ·
    refine ⟨69915697678093604200415041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93220930237458138933886721 69915697678093604200415041)
    ·
      refine ⟨52436773258570203150311281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69915697678093604200415041 52436773258570203150311281)
      ·
        refine ⟨39327579943927652362733461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52436773258570203150311281 39327579943927652362733461)
        ·
          refine ⟨1843480309871608704503131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39327579943927652362733461 1843480309871608704503131)
          ·
            refine ⟨2765220464807413056754697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1843480309871608704503131 2765220464807413056754697)
            ·
              refine ⟨2073915348605559792566023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2765220464807413056754697 2073915348605559792566023)
              ·
                refine ⟨3110873022908339688849035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2073915348605559792566023 3110873022908339688849035)
                ·
                  refine ⟨4666309534362509533273553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3110873022908339688849035 4666309534362509533273553)
                  ·
                    refine ⟨3499732150771882149955165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4666309534362509533273553 3499732150771882149955165)
                    ·
                      refine ⟨1312399556539455806233187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3499732150771882149955165 1312399556539455806233187)
                      ·
                        rfl

theorem cell23_2555889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 1, 2, 3].length) (baseStart_2555889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555889 prefixEnd_2555889 := by exact prefixLift 2555889
  have htrace : WordTrace (prefixWord ++ tailWord_2555889) baseStart_2555889 baseEnd_2555889 := by
    simpa [prefixWord, tailWord_2555889, baseEnd_2555889] using wordTrace_append hprefix tailTrace_2555889
  have hstable : (prefixWord ++ tailWord_2555889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555889).length < 2 ^ (prefixWord ++ tailWord_2555889).sum := by decide
  have hdescent : baseEnd_2555889 < baseStart_2555889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555901 : List Nat := [1, 4, 1, 1, 1, 2, 3, 2, 2, 6]
def baseStart_2555901 : Nat := 118140960795 + 2555901 * 2 ^ 59
def prefixEnd_2555901 : Nat := 4983230072969 + 3 ^ 40 * 2555901 * 2
def baseEnd_2555901 : Nat := 437468572769103253094377

theorem tailTrace_2555901 : CollatzResearch.WordTrace tailWord_2555901 prefixEnd_2555901 437468572769103253094377 := by
  unfold tailWord_2555901
  simp only [CollatzResearch.WordTrace]
  refine ⟨93221367913414664983323557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62147578608943109988882371 93221367913414664983323557)
  ·
    refine ⟨17479006483765249684373167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93221367913414664983323557 17479006483765249684373167)
    ·
      refine ⟨26218509725647874526559751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17479006483765249684373167 26218509725647874526559751)
      ·
        refine ⟨39327764588471811789839627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26218509725647874526559751 39327764588471811789839627)
        ·
          refine ⟨58991646882707717684759441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39327764588471811789839627 58991646882707717684759441)
          ·
            refine ⟨44243735162030788263569581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58991646882707717684759441 44243735162030788263569581)
            ·
              refine ⟨16591400685761545598838593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44243735162030788263569581 16591400685761545598838593)
              ·
                refine ⟨12443550514321159199128945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16591400685761545598838593 12443550514321159199128945)
                ·
                  refine ⟨9332662885740869399346709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12443550514321159199128945 9332662885740869399346709)
                  ·
                    refine ⟨437468572769103253094377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9332662885740869399346709 437468572769103253094377)
                    ·
                      rfl

theorem cell23_2555901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_2555901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555901 prefixEnd_2555901 := by exact prefixLift 2555901
  have htrace : WordTrace (prefixWord ++ tailWord_2555901) baseStart_2555901 baseEnd_2555901 := by
    simpa [prefixWord, tailWord_2555901, baseEnd_2555901] using wordTrace_append hprefix tailTrace_2555901
  have hstable : (prefixWord ++ tailWord_2555901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555901).length < 2 ^ (prefixWord ++ tailWord_2555901).sum := by decide
  have hdescent : baseEnd_2555901 < baseStart_2555901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555902 : List Nat := [4, 2, 2, 2, 1, 2, 1, 1, 4, 1, 3]
def baseStart_2555902 : Nat := 118140960795 + 2555902 * 2 ^ 59
def prefixEnd_2555902 : Nat := 4983230072969 + 3 ^ 40 * 2555902 * 2
def baseEnd_2555902 : Nat := 1312406231787964255370627

theorem tailTrace_2555902 : CollatzResearch.WordTrace tailWord_2555902 prefixEnd_2555902 1312406231787964255370627 := by
  unfold tailWord_2555902
  simp only [CollatzResearch.WordTrace]
  refine ⟨11652675548301380269263745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62147602924274028102739973 11652675548301380269263745)
  ·
    refine ⟨8739506661226035201947809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11652675548301380269263745 8739506661226035201947809)
    ·
      refine ⟨6554629995919526401460857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8739506661226035201947809 6554629995919526401460857)
      ·
        refine ⟨4915972496939644801095643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6554629995919526401460857 4915972496939644801095643)
        ·
          refine ⟨7373958745409467201643465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4915972496939644801095643 7373958745409467201643465)
          ·
            refine ⟨5530469059057100401232599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7373958745409467201643465 5530469059057100401232599)
            ·
              refine ⟨8295703588585650601848899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5530469059057100401232599 8295703588585650601848899)
              ·
                refine ⟨12443555382878475902773349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8295703588585650601848899 12443555382878475902773349)
                ·
                  refine ⟨2333166634289714231770003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12443555382878475902773349 2333166634289714231770003)
                  ·
                    refine ⟨3499749951434571347655005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2333166634289714231770003 3499749951434571347655005)
                    ·
                      refine ⟨1312406231787964255370627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3499749951434571347655005 1312406231787964255370627)
                      ·
                        rfl

theorem cell23_2555902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_2555902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555902 prefixEnd_2555902 := by exact prefixLift 2555902
  have htrace : WordTrace (prefixWord ++ tailWord_2555902) baseStart_2555902 baseEnd_2555902 := by
    simpa [prefixWord, tailWord_2555902, baseEnd_2555902] using wordTrace_append hprefix tailTrace_2555902
  have hstable : (prefixWord ++ tailWord_2555902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555902).length < 2 ^ (prefixWord ++ tailWord_2555902).sum := by decide
  have hdescent : baseEnd_2555902 < baseStart_2555902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555948 : List Nat := [2, 2, 1, 1, 1, 2, 2, 7, 5]
def baseStart_2555948 : Nat := 118140960795 + 2555948 * 2 ^ 59
def prefixEnd_2555948 : Nat := 4983230072969 + 3 ^ 40 * 2555948 * 2
def baseEnd_2555948 : Nat := 145825539099785675043935

theorem tailTrace_2555948 : CollatzResearch.WordTrace tailWord_2555948 prefixEnd_2555948 145825539099785675043935 := by
  unfold tailWord_2555948
  simp only [CollatzResearch.WordTrace]
  refine ⟨46611541072122196005142249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62148721429496261340189665 46611541072122196005142249)
  ·
    refine ⟨34958655804091647003856687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46611541072122196005142249 34958655804091647003856687)
    ·
      refine ⟨52437983706137470505785031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34958655804091647003856687 52437983706137470505785031)
      ·
        refine ⟨78656975559206205758677547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52437983706137470505785031 78656975559206205758677547)
        ·
          refine ⟨117985463338809308638016321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78656975559206205758677547 117985463338809308638016321)
          ·
            refine ⟨88489097504106981478512241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117985463338809308638016321 88489097504106981478512241)
            ·
              refine ⟨66366823128080236108884181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88489097504106981478512241 66366823128080236108884181)
              ·
                refine ⟨1555472417064380533801973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 66366823128080236108884181 1555472417064380533801973)
                ·
                  refine ⟨145825539099785675043935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1555472417064380533801973 145825539099785675043935)
                  ·
                    rfl

theorem cell23_2555948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7, 5].length) (baseStart_2555948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555948 prefixEnd_2555948 := by exact prefixLift 2555948
  have htrace : WordTrace (prefixWord ++ tailWord_2555948) baseStart_2555948 baseEnd_2555948 := by
    simpa [prefixWord, tailWord_2555948, baseEnd_2555948] using wordTrace_append hprefix tailTrace_2555948
  have hstable : (prefixWord ++ tailWord_2555948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555948).length < 2 ^ (prefixWord ++ tailWord_2555948).sum := by decide
  have hdescent : baseEnd_2555948 < baseStart_2555948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555958 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_2555958 : Nat := 118140960795 + 2555958 * 2 ^ 59
def prefixEnd_2555958 : Nat := 4983230072969 + 3 ^ 40 * 2555958 * 2
def baseEnd_2555958 : Nat := 1312434986704616036270369

theorem tailTrace_2555958 : CollatzResearch.WordTrace tailWord_2555958 prefixEnd_2555958 1312434986704616036270369 := by
  unfold tailWord_2555958
  simp only [CollatzResearch.WordTrace]
  refine ⟨5826465429638010232384283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62148964582805442478765685 5826465429638010232384283)
  ·
    refine ⟨8739698144457015348576425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5826465429638010232384283 8739698144457015348576425)
    ·
      refine ⟨6554773608342761511432319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8739698144457015348576425 6554773608342761511432319)
      ·
        refine ⟨9832160412514142267148479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6554773608342761511432319 9832160412514142267148479)
        ·
          refine ⟨14748240618771213400722719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9832160412514142267148479 14748240618771213400722719)
          ·
            refine ⟨22122360928156820101084079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14748240618771213400722719 22122360928156820101084079)
            ·
              refine ⟨33183541392235230151626119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22122360928156820101084079 33183541392235230151626119)
              ·
                refine ⟨49775312088352845227439179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33183541392235230151626119 49775312088352845227439179)
                ·
                  refine ⟨74662968132529267841158769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49775312088352845227439179 74662968132529267841158769)
                  ·
                    refine ⟨55997226099396950880869077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74662968132529267841158769 55997226099396950880869077)
                    ·
                      refine ⟨1312434986704616036270369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55997226099396950880869077 1312434986704616036270369)
                      ·
                        rfl

theorem cell23_2555958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_2555958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555958 prefixEnd_2555958 := by exact prefixLift 2555958
  have htrace : WordTrace (prefixWord ++ tailWord_2555958) baseStart_2555958 baseEnd_2555958 := by
    simpa [prefixWord, tailWord_2555958, baseEnd_2555958] using wordTrace_append hprefix tailTrace_2555958
  have hstable : (prefixWord ++ tailWord_2555958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555958).length < 2 ^ (prefixWord ++ tailWord_2555958).sum := by decide
  have hdescent : baseEnd_2555958 < baseStart_2555958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2555991 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 2, 8]
def baseStart_2555991 : Nat := 118140960795 + 2555991 * 2 ^ 59
def prefixEnd_2555991 : Nat := 4983230072969 + 3 ^ 40 * 2555991 * 2
def baseEnd_2555991 : Nat := 437483977188738135719239

theorem tailTrace_2555991 : CollatzResearch.WordTrace tailWord_2555991 prefixEnd_2555991 437483977188738135719239 := by
  unfold tailWord_2555991
  simp only [CollatzResearch.WordTrace]
  refine ⟨93224650483088610354099827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62149766988725740236066551 93224650483088610354099827)
  ·
    refine ⟨139836975724632915531149741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93224650483088610354099827 139836975724632915531149741)
    ·
      refine ⟨52438865896737343324181153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139836975724632915531149741 52438865896737343324181153)
      ·
        refine ⟨39329149422553007493135865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52438865896737343324181153 39329149422553007493135865)
        ·
          refine ⟨29496862066914755619851899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39329149422553007493135865 29496862066914755619851899)
          ·
            refine ⟨44245293100372133429777849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29496862066914755619851899 44245293100372133429777849)
            ·
              refine ⟨33183969825279100072333387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44245293100372133429777849 33183969825279100072333387)
              ·
                refine ⟨49775954737918650108500081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33183969825279100072333387 49775954737918650108500081)
                ·
                  refine ⟨37331966053438987581375061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49775954737918650108500081 37331966053438987581375061)
                  ·
                    refine ⟨437483977188738135719239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37331966053438987581375061 437483977188738135719239)
                    ·
                      rfl

theorem cell23_2555991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 8].length) (baseStart_2555991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2555991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2555991 prefixEnd_2555991 := by exact prefixLift 2555991
  have htrace : WordTrace (prefixWord ++ tailWord_2555991) baseStart_2555991 baseEnd_2555991 := by
    simpa [prefixWord, tailWord_2555991, baseEnd_2555991] using wordTrace_append hprefix tailTrace_2555991
  have hstable : (prefixWord ++ tailWord_2555991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2555991).length < 2 ^ (prefixWord ++ tailWord_2555991).sum := by decide
  have hdescent : baseEnd_2555991 < baseStart_2555991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2555991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556082 : List Nat := [3, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3]
def baseStart_2556082 : Nat := 118140960795 + 2556082 * 2 ^ 59
def prefixEnd_2556082 : Nat := 4983230072969 + 3 ^ 40 * 2556082 * 2
def baseEnd_2556082 : Nat := 1312498658305773551119799

theorem tailTrace_2556082 : CollatzResearch.WordTrace tailWord_2556082 prefixEnd_2556082 1312498658305773551119799 := by
  unfold tailWord_2556082
  simp only [CollatzResearch.WordTrace]
  refine ⟨23306992381439733223915625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62151979683839288597108333 23306992381439733223915625)
  ·
    refine ⟨17480244286079799917936719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23306992381439733223915625 17480244286079799917936719)
    ·
      refine ⟨26220366429119699876905079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17480244286079799917936719 26220366429119699876905079)
      ·
        refine ⟨39330549643679549815357619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26220366429119699876905079 39330549643679549815357619)
        ·
          refine ⟨58995824465519324723036429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39330549643679549815357619 58995824465519324723036429)
          ·
            refine ⟨22123434174569746771138661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58995824465519324723036429 22123434174569746771138661)
            ·
              refine ⟨4148143907731827519588499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22123434174569746771138661 4148143907731827519588499)
              ·
                refine ⟨6222215861597741279382749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4148143907731827519588499 6222215861597741279382749)
                ·
                  refine ⟨2333330948099152979768531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6222215861597741279382749 2333330948099152979768531)
                  ·
                    refine ⟨3499996422148729469652797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2333330948099152979768531 3499996422148729469652797)
                    ·
                      refine ⟨1312498658305773551119799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3499996422148729469652797 1312498658305773551119799)
                      ·
                        rfl

theorem cell23_2556082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_2556082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556082 prefixEnd_2556082 := by exact prefixLift 2556082
  have htrace : WordTrace (prefixWord ++ tailWord_2556082) baseStart_2556082 baseEnd_2556082 := by
    simpa [prefixWord, tailWord_2556082, baseEnd_2556082] using wordTrace_append hprefix tailTrace_2556082
  have hstable : (prefixWord ++ tailWord_2556082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556082).length < 2 ^ (prefixWord ++ tailWord_2556082).sum := by decide
  have hdescent : baseEnd_2556082 < baseStart_2556082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556122 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2]
def baseStart_2556122 : Nat := 118140960795 + 2556122 * 2 ^ 59
def prefixEnd_2556122 : Nat := 4983230072969 + 3 ^ 40 * 2556122 * 2
def baseEnd_2556122 : Nat := 1312519197531953394619615

theorem tailTrace_2556122 : CollatzResearch.WordTrace tailWord_2556122 prefixEnd_2556122 1312519197531953394619615 := by
  unfold tailWord_2556122
  simp only [CollatzResearch.WordTrace]
  refine ⟨23307357111403504931779655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62152952297076013151412413 23307357111403504931779655)
  ·
    refine ⟨34961035667105257397669483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23307357111403504931779655 34961035667105257397669483)
    ·
      refine ⟨52441553500657886096504225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34961035667105257397669483 52441553500657886096504225)
      ·
        refine ⟨39331165125493414572378169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52441553500657886096504225 39331165125493414572378169)
        ·
          refine ⟨29498373844120060929283627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39331165125493414572378169 29498373844120060929283627)
          ·
            refine ⟨44247560766180091393925441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29498373844120060929283627 44247560766180091393925441)
            ·
              refine ⟨33185670574635068545444081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44247560766180091393925441 33185670574635068545444081)
              ·
                refine ⟨24889252930976301409083061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33185670574635068545444081 24889252930976301409083061)
                ·
                  refine ⟨2333367462279028257101537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24889252930976301409083061 2333367462279028257101537)
                  ·
                    refine ⟨1750025596709271192826153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2333367462279028257101537 1750025596709271192826153)
                    ·
                      refine ⟨1312519197531953394619615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1750025596709271192826153 1312519197531953394619615)
                      ·
                        rfl

theorem cell23_2556122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2].length) (baseStart_2556122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556122 prefixEnd_2556122 := by exact prefixLift 2556122
  have htrace : WordTrace (prefixWord ++ tailWord_2556122) baseStart_2556122 baseEnd_2556122 := by
    simpa [prefixWord, tailWord_2556122, baseEnd_2556122] using wordTrace_append hprefix tailTrace_2556122
  have hstable : (prefixWord ++ tailWord_2556122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556122).length < 2 ^ (prefixWord ++ tailWord_2556122).sum := by decide
  have hdescent : baseEnd_2556122 < baseStart_2556122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556135 : List Nat := [1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 6]
def baseStart_2556135 : Nat := 118140960795 + 2556135 * 2 ^ 59
def prefixEnd_2556135 : Nat := 4983230072969 + 3 ^ 40 * 2556135 * 2
def baseEnd_2556135 : Nat := 1312525872780461843757055

theorem tailTrace_2556135 : CollatzResearch.WordTrace tailWord_2556135 prefixEnd_2556135 1312525872780461843757055 := by
  unfold tailWord_2556135
  simp only [CollatzResearch.WordTrace]
  refine ⟨93229902594566922947341859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62153268396377948631561239 93229902594566922947341859)
  ·
    refine ⟨139844853891850384421012789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93229902594566922947341859 139844853891850384421012789)
    ·
      refine ⟨13110455052360973539469949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 139844853891850384421012789 13110455052360973539469949)
      ·
        refine ⟨4916420644635365077301231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13110455052360973539469949 4916420644635365077301231)
        ·
          refine ⟨7374630966953047615951847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4916420644635365077301231 7374630966953047615951847)
          ·
            refine ⟨11061946450429571423927771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7374630966953047615951847 11061946450429571423927771)
            ·
              refine ⟨16592919675644357135891657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11061946450429571423927771 16592919675644357135891657)
              ·
                refine ⟨12444689756733267851918743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16592919675644357135891657 12444689756733267851918743)
                ·
                  refine ⟨18667034635099901777878115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12444689756733267851918743 18667034635099901777878115)
                  ·
                    refine ⟨28000551952649852666817173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18667034635099901777878115 28000551952649852666817173)
                    ·
                      refine ⟨1312525872780461843757055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28000551952649852666817173 1312525872780461843757055)
                      ·
                        rfl

theorem cell23_2556135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_2556135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556135 prefixEnd_2556135 := by exact prefixLift 2556135
  have htrace : WordTrace (prefixWord ++ tailWord_2556135) baseStart_2556135 baseEnd_2556135 := by
    simpa [prefixWord, tailWord_2556135, baseEnd_2556135] using wordTrace_append hprefix tailTrace_2556135
  have hstable : (prefixWord ++ tailWord_2556135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556135).length < 2 ^ (prefixWord ++ tailWord_2556135).sum := by decide
  have hdescent : baseEnd_2556135 < baseStart_2556135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556190 : List Nat := [4, 3, 2, 1, 1, 2, 1, 4, 1, 2, 2]
def baseStart_2556190 : Nat := 118140960795 + 2556190 * 2 ^ 59
def prefixEnd_2556190 : Nat := 4983230072969 + 3 ^ 40 * 2556190 * 2
def baseEnd_2556190 : Nat := 1312554114216459128569303

theorem tailTrace_2556190 : CollatzResearch.WordTrace tailWord_2556190 prefixEnd_2556190 1312554114216459128569303 := by
  unfold tailWord_2556190
  simp only [CollatzResearch.WordTrace]
  refine ⟨11653988576170958417574253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62154605739578444893729349 11653988576170958417574253)
  ·
    refine ⟨4370245716064109406590345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11653988576170958417574253 4370245716064109406590345)
    ·
      refine ⟨3277684287048082054942759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4370245716064109406590345 3277684287048082054942759)
      ·
        refine ⟨4916526430572123082414139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3277684287048082054942759 4916526430572123082414139)
        ·
          refine ⟨7374789645858184623621209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4916526430572123082414139 7374789645858184623621209)
          ·
            refine ⟨5531092234393638467715907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7374789645858184623621209 5531092234393638467715907)
            ·
              refine ⟨8296638351590457701573861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5531092234393638467715907 8296638351590457701573861)
              ·
                refine ⟨1555619690923210819045099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8296638351590457701573861 1555619690923210819045099)
                ·
                  refine ⟨2333429536384816228567649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1555619690923210819045099 2333429536384816228567649)
                  ·
                    refine ⟨1750072152288612171425737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2333429536384816228567649 1750072152288612171425737)
                    ·
                      refine ⟨1312554114216459128569303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1750072152288612171425737 1312554114216459128569303)
                      ·
                        rfl

theorem cell23_2556190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_2556190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556190 prefixEnd_2556190 := by exact prefixLift 2556190
  have htrace : WordTrace (prefixWord ++ tailWord_2556190) baseStart_2556190 baseEnd_2556190 := by
    simpa [prefixWord, tailWord_2556190, baseEnd_2556190] using wordTrace_append hprefix tailTrace_2556190
  have hstable : (prefixWord ++ tailWord_2556190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556190).length < 2 ^ (prefixWord ++ tailWord_2556190).sum := by decide
  have hdescent : baseEnd_2556190 < baseStart_2556190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556206 : List Nat := [4, 1, 3, 3, 1, 1, 2, 1, 1, 3, 3]
def baseStart_2556206 : Nat := 118140960795 + 2556206 * 2 ^ 59
def prefixEnd_2556206 : Nat := 4983230072969 + 3 ^ 40 * 2556206 * 2
def baseEnd_2556206 : Nat := 1312562329906931065969229

theorem tailTrace_2556206 : CollatzResearch.WordTrace tailWord_2556206 prefixEnd_2556206 1312562329906931065969229 := by
  unfold tailWord_2556206
  simp only [CollatzResearch.WordTrace]
  refine ⟨11654061522163712759147059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62154994784873134715450981 11654061522163712759147059)
  ·
    refine ⟨17481092283245569138720589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11654061522163712759147059 17481092283245569138720589)
    ·
      refine ⟨6555409606217088427020221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17481092283245569138720589 6555409606217088427020221)
      ·
        refine ⟨2458278602331408160132583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6555409606217088427020221 2458278602331408160132583)
        ·
          refine ⟨3687417903497112240198875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2458278602331408160132583 3687417903497112240198875)
          ·
            refine ⟨5531126855245668360298313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3687417903497112240198875 5531126855245668360298313)
            ·
              refine ⟨4148345141434251270223735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5531126855245668360298313 4148345141434251270223735)
              ·
                refine ⟨6222517712151376905335603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4148345141434251270223735 6222517712151376905335603)
                ·
                  refine ⟨9333776568227065358003405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6222517712151376905335603 9333776568227065358003405)
                  ·
                    refine ⟨3500166213085149509251277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9333776568227065358003405 3500166213085149509251277)
                    ·
                      refine ⟨1312562329906931065969229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3500166213085149509251277 1312562329906931065969229)
                      ·
                        rfl

theorem cell23_2556206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_2556206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556206 prefixEnd_2556206 := by exact prefixLift 2556206
  have htrace : WordTrace (prefixWord ++ tailWord_2556206) baseStart_2556206 baseEnd_2556206 := by
    simpa [prefixWord, tailWord_2556206, baseEnd_2556206] using wordTrace_append hprefix tailTrace_2556206
  have hstable : (prefixWord ++ tailWord_2556206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556206).length < 2 ^ (prefixWord ++ tailWord_2556206).sum := by decide
  have hdescent : baseEnd_2556206 < baseStart_2556206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556263 : List Nat := [1, 1, 5, 1, 3, 2, 3, 1, 2, 2, 2]
def baseStart_2556263 : Nat := 118140960795 + 2556263 * 2 ^ 59
def prefixEnd_2556263 : Nat := 4983230072969 + 3 ^ 40 * 2556263 * 2
def baseEnd_2556263 : Nat := 1312591598304237342956467

theorem tailTrace_2556263 : CollatzResearch.WordTrace tailWord_2556263 prefixEnd_2556263 1312591598304237342956467 := by
  unfold tailWord_2556263
  simp only [CollatzResearch.WordTrace]
  refine ⟨93234571138103200808001443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62156380758735467205334295 93234571138103200808001443)
  ·
    refine ⟨139851856707154801212002165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93234571138103200808001443 139851856707154801212002165)
    ·
      refine ⟨13111111566295762613625203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 139851856707154801212002165 13111111566295762613625203)
      ·
        refine ⟨19666667349443643920437805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13111111566295762613625203 19666667349443643920437805)
        ·
          refine ⟨7375000256041366470164177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19666667349443643920437805 7375000256041366470164177)
          ·
            refine ⟨5531250192031024852623133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7375000256041366470164177 5531250192031024852623133)
            ·
              refine ⟨2074218822011634319733675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5531250192031024852623133 2074218822011634319733675)
              ·
                refine ⟨3111328233017451479600513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2074218822011634319733675 3111328233017451479600513)
                ·
                  refine ⟨2333496174763088609700385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3111328233017451479600513 2333496174763088609700385)
                  ·
                    refine ⟨1750122131072316457275289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2333496174763088609700385 1750122131072316457275289)
                    ·
                      refine ⟨1312591598304237342956467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1750122131072316457275289 1312591598304237342956467)
                      ·
                        rfl

theorem cell23_2556263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_2556263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556263 prefixEnd_2556263 := by exact prefixLift 2556263
  have htrace : WordTrace (prefixWord ++ tailWord_2556263) baseStart_2556263 baseEnd_2556263 := by
    simpa [prefixWord, tailWord_2556263, baseEnd_2556263] using wordTrace_append hprefix tailTrace_2556263
  have hstable : (prefixWord ++ tailWord_2556263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556263).length < 2 ^ (prefixWord ++ tailWord_2556263).sum := by decide
  have hdescent : baseEnd_2556263 < baseStart_2556263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556412 : List Nat := [2, 2, 2, 1, 2, 1, 1, 5, 1, 1, 5]
def baseStart_2556412 : Nat := 118140960795 + 2556412 * 2 ^ 59
def prefixEnd_2556412 : Nat := 4983230072969 + 3 ^ 40 * 2556412 * 2
def baseEnd_2556412 : Nat := 1312668106921757259993281

theorem tailTrace_2556412 : CollatzResearch.WordTrace tailWord_2556412 prefixEnd_2556412 1312668106921757259993281 := by
  unfold tailWord_2556412
  simp only [CollatzResearch.WordTrace]
  refine ⟨46620002807281699627587745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62160003743042266170116993 46620002807281699627587745)
  ·
    refine ⟨34965002105461274720690809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46620002807281699627587745 34965002105461274720690809)
    ·
      refine ⟨26223751579095956040518107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34965002105461274720690809 26223751579095956040518107)
      ·
        refine ⟨39335627368643934060777161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26223751579095956040518107 39335627368643934060777161)
        ·
          refine ⟨29501720526482950545582871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39335627368643934060777161 29501720526482950545582871)
          ·
            refine ⟨44252580789724425818374307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29501720526482950545582871 44252580789724425818374307)
            ·
              refine ⟨66378871184586638727561461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44252580789724425818374307 66378871184586638727561461)
              ·
                refine ⟨6223019173554997380708887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66378871184586638727561461 6223019173554997380708887)
                ·
                  refine ⟨9334528760332496071063331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6223019173554997380708887 9334528760332496071063331)
                  ·
                    refine ⟨14001793140498744106594997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9334528760332496071063331 14001793140498744106594997)
                    ·
                      refine ⟨1312668106921757259993281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14001793140498744106594997 1312668106921757259993281)
                      ·
                        rfl

theorem cell23_2556412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_2556412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556412 prefixEnd_2556412 := by exact prefixLift 2556412
  have htrace : WordTrace (prefixWord ++ tailWord_2556412) baseStart_2556412 baseEnd_2556412 := by
    simpa [prefixWord, tailWord_2556412, baseEnd_2556412] using wordTrace_append hprefix tailTrace_2556412
  have hstable : (prefixWord ++ tailWord_2556412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556412).length < 2 ^ (prefixWord ++ tailWord_2556412).sum := by decide
  have hdescent : baseEnd_2556412 < baseStart_2556412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556415 : List Nat := [1, 1, 2, 2, 1, 2, 14]
def baseStart_2556415 : Nat := 118140960795 + 2556415 * 2 ^ 59
def prefixEnd_2556415 : Nat := 4983230072969 + 3 ^ 40 * 2556415 * 2
def baseEnd_2556415 : Nat := 16205798115601490719207

theorem tailTrace_2556415 : CollatzResearch.WordTrace tailWord_2556415 prefixEnd_2556415 16205798115601490719207 := by
  unfold tailWord_2556415
  simp only [CollatzResearch.WordTrace]
  refine ⟨93240115033552530767534699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62160076689035020511689799 93240115033552530767534699)
  ·
    refine ⟨139860172550328796151302049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93240115033552530767534699 139860172550328796151302049)
    ·
      refine ⟨104895129412746597113476537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139860172550328796151302049 104895129412746597113476537)
      ·
        refine ⟨78671347059559947835107403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104895129412746597113476537 78671347059559947835107403)
        ·
          refine ⟨118007020589339921752661105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78671347059559947835107403 118007020589339921752661105)
          ·
            refine ⟨88505265442004941314495829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118007020589339921752661105 88505265442004941314495829)
            ·
              refine ⟨16205798115601490719207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 88505265442004941314495829 16205798115601490719207)
              ·
                rfl

theorem cell23_2556415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 14].length) (baseStart_2556415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556415 prefixEnd_2556415 := by exact prefixLift 2556415
  have htrace : WordTrace (prefixWord ++ tailWord_2556415) baseStart_2556415 baseEnd_2556415 := by
    simpa [prefixWord, tailWord_2556415, baseEnd_2556415] using wordTrace_append hprefix tailTrace_2556415
  have hstable : (prefixWord ++ tailWord_2556415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556415).length < 2 ^ (prefixWord ++ tailWord_2556415).sum := by decide
  have hdescent : baseEnd_2556415 < baseStart_2556415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556436 : List Nat := [2, 4, 3, 1, 1, 1, 3, 1, 1, 6]
def baseStart_2556436 : Nat := 118140960795 + 2556436 * 2 ^ 59
def prefixEnd_2556436 : Nat := 4983230072969 + 3 ^ 40 * 2556436 * 2
def baseEnd_2556436 : Nat := 437560143485821722031057

theorem tailTrace_2556436 : CollatzResearch.WordTrace tailWord_2556436 prefixEnd_2556436 437560143485821722031057 := by
  unfold tailWord_2556436
  simp only [CollatzResearch.WordTrace]
  refine ⟨46620440483238225677024581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62160587310984300902699441 46620440483238225677024581)
  ·
    refine ⟨8741332590607167314442109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46620440483238225677024581 8741332590607167314442109)
    ·
      refine ⟨3277999721477687742915791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8741332590607167314442109 3277999721477687742915791)
      ·
        refine ⟨4916999582216531614373687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3277999721477687742915791 4916999582216531614373687)
        ·
          refine ⟨7375499373324797421560531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4916999582216531614373687 7375499373324797421560531)
          ·
            refine ⟨11063249059987196132340797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7375499373324797421560531 11063249059987196132340797)
            ·
              refine ⟨4148718397495198549627799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11063249059987196132340797 4148718397495198549627799)
              ·
                refine ⟨6223077596242797824441699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4148718397495198549627799 6223077596242797824441699)
                ·
                  refine ⟨9334616394364196736662549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6223077596242797824441699 9334616394364196736662549)
                  ·
                    refine ⟨437560143485821722031057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9334616394364196736662549 437560143485821722031057)
                    ·
                      rfl

theorem cell23_2556436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_2556436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556436 prefixEnd_2556436 := by exact prefixLift 2556436
  have htrace : WordTrace (prefixWord ++ tailWord_2556436) baseStart_2556436 baseEnd_2556436 := by
    simpa [prefixWord, tailWord_2556436, baseEnd_2556436] using wordTrace_append hprefix tailTrace_2556436
  have hstable : (prefixWord ++ tailWord_2556436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556436).length < 2 ^ (prefixWord ++ tailWord_2556436).sum := by decide
  have hdescent : baseEnd_2556436 < baseStart_2556436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556472 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 2, 2, 5]
def baseStart_2556472 : Nat := 118140960795 + 2556472 * 2 ^ 59
def prefixEnd_2556472 : Nat := 4983230072969 + 3 ^ 40 * 2556472 * 2
def baseEnd_2556472 : Nat := 1312698915761027025243005

theorem tailTrace_2556472 : CollatzResearch.WordTrace tailWord_2556472 prefixEnd_2556472 1312698915761027025243005 := by
  unfold tailWord_2556472
  simp only [CollatzResearch.WordTrace]
  refine ⟨46621096997173014751179835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62161462662897353001573113 46621096997173014751179835)
  ·
    refine ⟨69931645495759522126769753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46621096997173014751179835 69931645495759522126769753)
    ·
      refine ⟨52448734121819641595077315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69931645495759522126769753 52448734121819641595077315)
      ·
        refine ⟨78673101182729462392615973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52448734121819641595077315 78673101182729462392615973)
        ·
          refine ⟨14751206471761774198615495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78673101182729462392615973 14751206471761774198615495)
          ·
            refine ⟨22126809707642661297923243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14751206471761774198615495 22126809707642661297923243)
            ·
              refine ⟨33190214561463991946884865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22126809707642661297923243 33190214561463991946884865)
              ·
                refine ⟨24892660921097993960163649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33190214561463991946884865 24892660921097993960163649)
                ·
                  refine ⟨18669495690823495470122737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24892660921097993960163649 18669495690823495470122737)
                  ·
                    refine ⟨14002121768117621602592053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18669495690823495470122737 14002121768117621602592053)
                    ·
                      refine ⟨1312698915761027025243005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14002121768117621602592053 1312698915761027025243005)
                      ·
                        rfl

theorem cell23_2556472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_2556472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556472 prefixEnd_2556472 := by exact prefixLift 2556472
  have htrace : WordTrace (prefixWord ++ tailWord_2556472) baseStart_2556472 baseEnd_2556472 := by
    simpa [prefixWord, tailWord_2556472, baseEnd_2556472] using wordTrace_append hprefix tailTrace_2556472
  have hstable : (prefixWord ++ tailWord_2556472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556472).length < 2 ^ (prefixWord ++ tailWord_2556472).sum := by decide
  have hdescent : baseEnd_2556472 < baseStart_2556472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556476 : List Nat := [2, 2, 2, 2, 3, 1, 2, 1, 4, 1, 3]
def baseStart_2556476 : Nat := 118140960795 + 2556476 * 2 ^ 59
def prefixEnd_2556476 : Nat := 4983230072969 + 3 ^ 40 * 2556476 * 2
def baseEnd_2556476 : Nat := 1312700969683645009592987

theorem tailTrace_2556476 : CollatzResearch.WordTrace tailWord_2556476 prefixEnd_2556476 1312700969683645009592987 := by
  unfold tailWord_2556476
  simp only [CollatzResearch.WordTrace]
  refine ⟨46621169943165769092752641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62161559924221025457003521 46621169943165769092752641)
  ·
    refine ⟨34965877457374326819564481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46621169943165769092752641 34965877457374326819564481)
    ·
      refine ⟨26224408093030745114673361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34965877457374326819564481 26224408093030745114673361)
      ·
        refine ⟨19668306069773058836005021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26224408093030745114673361 19668306069773058836005021)
        ·
          refine ⟨7375614776164897063501883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19668306069773058836005021 7375614776164897063501883)
          ·
            refine ⟨11063422164247345595252825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7375614776164897063501883 11063422164247345595252825)
            ·
              refine ⟨8297566623185509196439619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11063422164247345595252825 8297566623185509196439619)
              ·
                refine ⟨12446349934778263794659429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8297566623185509196439619 12446349934778263794659429)
                ·
                  refine ⟨2333690612770924461498643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12446349934778263794659429 2333690612770924461498643)
                  ·
                    refine ⟨3500535919156386692247965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2333690612770924461498643 3500535919156386692247965)
                    ·
                      refine ⟨1312700969683645009592987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3500535919156386692247965 1312700969683645009592987)
                      ·
                        rfl

theorem cell23_2556476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_2556476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556476 prefixEnd_2556476 := by exact prefixLift 2556476
  have htrace : WordTrace (prefixWord ++ tailWord_2556476) baseStart_2556476 baseEnd_2556476 := by
    simpa [prefixWord, tailWord_2556476, baseEnd_2556476] using wordTrace_append hprefix tailTrace_2556476
  have hstable : (prefixWord ++ tailWord_2556476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556476).length < 2 ^ (prefixWord ++ tailWord_2556476).sum := by decide
  have hdescent : baseEnd_2556476 < baseStart_2556476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556477 : List Nat := [1, 4, 1, 3, 2, 2, 3, 2, 1, 2, 2]
def baseStart_2556477 : Nat := 118140960795 + 2556477 * 2 ^ 59
def prefixEnd_2556477 : Nat := 4983230072969 + 3 ^ 40 * 2556477 * 2
def baseEnd_2556477 : Nat := 1312701483164299505680483

theorem tailTrace_2556477 : CollatzResearch.WordTrace tailWord_2556477 prefixEnd_2556477 1312701483164299505680483 := by
  unfold tailWord_2556477
  simp only [CollatzResearch.WordTrace]
  refine ⟨93242376359327915356291685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62161584239551943570861123 93242376359327915356291685)
  ·
    refine ⟨17482945567373984129304691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93242376359327915356291685 17482945567373984129304691)
    ·
      refine ⟨26224418351060976193957037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17482945567373984129304691 26224418351060976193957037)
      ·
        refine ⟨9834156881647866072733889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26224418351060976193957037 9834156881647866072733889)
        ·
          refine ⟨7375617661235899554550417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9834156881647866072733889 7375617661235899554550417)
          ·
            refine ⟨5531713245926924665912813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7375617661235899554550417 5531713245926924665912813)
            ·
              refine ⟨2074392467222596749717305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5531713245926924665912813 2074392467222596749717305)
              ·
                refine ⟨1555794350416947562287979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2074392467222596749717305 1555794350416947562287979)
                ·
                  refine ⟨2333691525625421343431969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1555794350416947562287979 2333691525625421343431969)
                  ·
                    refine ⟨1750268644219066007573977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2333691525625421343431969 1750268644219066007573977)
                    ·
                      refine ⟨1312701483164299505680483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1750268644219066007573977 1312701483164299505680483)
                      ·
                        rfl

theorem cell23_2556477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_2556477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556477 prefixEnd_2556477 := by exact prefixLift 2556477
  have htrace : WordTrace (prefixWord ++ tailWord_2556477) baseStart_2556477 baseEnd_2556477 := by
    simpa [prefixWord, tailWord_2556477, baseEnd_2556477] using wordTrace_append hprefix tailTrace_2556477
  have hstable : (prefixWord ++ tailWord_2556477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556477).length < 2 ^ (prefixWord ++ tailWord_2556477).sum := by decide
  have hdescent : baseEnd_2556477 < baseStart_2556477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556492 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 1, 8]
def baseStart_2556492 : Nat := 118140960795 + 2556492 * 2 ^ 59
def prefixEnd_2556492 : Nat := 4983230072969 + 3 ^ 40 * 2556492 * 2
def baseEnd_2556492 : Nat := 437569728458038982330971

theorem tailTrace_2556492 : CollatzResearch.WordTrace tailWord_2556492 prefixEnd_2556492 437569728458038982330971 := by
  unfold tailWord_2556492
  simp only [CollatzResearch.WordTrace]
  refine ⟨46621461727136786459043865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62161948969515715278725153 46621461727136786459043865)
  ·
    refine ⟨34966096295352589844282899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46621461727136786459043865 34966096295352589844282899)
    ·
      refine ⟨52449144443028884766424349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34966096295352589844282899 52449144443028884766424349)
      ·
        refine ⟨19668429166135831787409131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52449144443028884766424349 19668429166135831787409131)
        ·
          refine ⟨29502643749203747681113697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19668429166135831787409131 29502643749203747681113697)
          ·
            refine ⟨22126982811902810760835273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29502643749203747681113697 22126982811902810760835273)
            ·
              refine ⟨16595237108927108070626455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22126982811902810760835273 16595237108927108070626455)
              ·
                refine ⟨24892855663390662105939683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16595237108927108070626455 24892855663390662105939683)
                ·
                  refine ⟨37339283495085993158909525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24892855663390662105939683 37339283495085993158909525)
                  ·
                    refine ⟨437569728458038982330971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37339283495085993158909525 437569728458038982330971)
                    ·
                      rfl

theorem cell23_2556492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 1, 8].length) (baseStart_2556492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556492 prefixEnd_2556492 := by exact prefixLift 2556492
  have htrace : WordTrace (prefixWord ++ tailWord_2556492) baseStart_2556492 baseEnd_2556492 := by
    simpa [prefixWord, tailWord_2556492, baseEnd_2556492] using wordTrace_append hprefix tailTrace_2556492
  have hstable : (prefixWord ++ tailWord_2556492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556492).length < 2 ^ (prefixWord ++ tailWord_2556492).sum := by decide
  have hdescent : baseEnd_2556492 < baseStart_2556492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556516 : List Nat := [2, 3, 1, 1, 2, 2, 3, 2, 1, 4, 2]
def baseStart_2556516 : Nat := 118140960795 + 2556516 * 2 ^ 59
def prefixEnd_2556516 : Nat := 4983230072969 + 3 ^ 40 * 2556516 * 2
def baseEnd_2556516 : Nat := 1312721508909824853092803

theorem tailTrace_2556516 : CollatzResearch.WordTrace tailWord_2556516 prefixEnd_2556516 1312721508909824853092803 := by
  unfold tailWord_2556516
  simp only [CollatzResearch.WordTrace]
  refine ⟨46621899403093312508480701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62162532537457750011307601 46621899403093312508480701)
  ·
    refine ⟨17483212276159992190680263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46621899403093312508480701 17483212276159992190680263)
    ·
      refine ⟨26224818414239988286020395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17483212276159992190680263 26224818414239988286020395)
      ·
        refine ⟨39337227621359982429030593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26224818414239988286020395 39337227621359982429030593)
        ·
          refine ⟨29502920716019986821772945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39337227621359982429030593 29502920716019986821772945)
          ·
            refine ⟨22127190537014990116329709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29502920716019986821772945 22127190537014990116329709)
            ·
              refine ⟨8297696451380621293623641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22127190537014990116329709 8297696451380621293623641)
              ·
                refine ⟨6223272338535465970217731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8297696451380621293623641 6223272338535465970217731)
                ·
                  refine ⟨9334908507803198955326597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6223272338535465970217731 9334908507803198955326597)
                  ·
                    refine ⟨1750295345213099804123737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9334908507803198955326597 1750295345213099804123737)
                    ·
                      refine ⟨1312721508909824853092803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1750295345213099804123737 1312721508909824853092803)
                      ·
                        rfl

theorem cell23_2556516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 1, 4, 2].length) (baseStart_2556516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556516 prefixEnd_2556516 := by exact prefixLift 2556516
  have htrace : WordTrace (prefixWord ++ tailWord_2556516) baseStart_2556516 baseEnd_2556516 := by
    simpa [prefixWord, tailWord_2556516, baseEnd_2556516] using wordTrace_append hprefix tailTrace_2556516
  have hstable : (prefixWord ++ tailWord_2556516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556516).length < 2 ^ (prefixWord ++ tailWord_2556516).sum := by decide
  have hdescent : baseEnd_2556516 < baseStart_2556516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556549 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 1, 5, 3]
def baseStart_2556549 : Nat := 118140960795 + 2556549 * 2 ^ 59
def prefixEnd_2556549 : Nat := 4983230072969 + 3 ^ 40 * 2556549 * 2
def baseEnd_2556549 : Nat := 1312738453771423223980151

theorem tailTrace_2556549 : CollatzResearch.WordTrace tailWord_2556549 prefixEnd_2556549 1312738453771423223980151 := by
  unfold tailWord_2556549
  simp only [CollatzResearch.WordTrace]
  refine ⟨93245002415067071652912701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62163334943378047768608467 93245002415067071652912701)
  ·
    refine ⟨34966875905650151869842263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93245002415067071652912701 34966875905650151869842263)
    ·
      refine ⟨52450313858475227804763395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34966875905650151869842263 52450313858475227804763395)
      ·
        refine ⟨78675470787712841707145093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52450313858475227804763395 78675470787712841707145093)
        ·
          refine ⟨14751650772696157820089705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78675470787712841707145093 14751650772696157820089705)
          ·
            refine ⟨11063738079522118365067279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14751650772696157820089705 11063738079522118365067279)
            ·
              refine ⟨16595607119283177547600919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11063738079522118365067279 16595607119283177547600919)
              ·
                refine ⟨24893410678924766321401379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16595607119283177547600919 24893410678924766321401379)
                ·
                  refine ⟨37340116018387149482102069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24893410678924766321401379 37340116018387149482102069)
                  ·
                    refine ⟨3500635876723795263947069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37340116018387149482102069 3500635876723795263947069)
                    ·
                      refine ⟨1312738453771423223980151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3500635876723795263947069 1312738453771423223980151)
                      ·
                        rfl

theorem cell23_2556549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 5, 3].length) (baseStart_2556549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556549 prefixEnd_2556549 := by exact prefixLift 2556549
  have htrace : WordTrace (prefixWord ++ tailWord_2556549) baseStart_2556549 baseEnd_2556549 := by
    simpa [prefixWord, tailWord_2556549, baseEnd_2556549] using wordTrace_append hprefix tailTrace_2556549
  have hstable : (prefixWord ++ tailWord_2556549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556549).length < 2 ^ (prefixWord ++ tailWord_2556549).sum := by decide
  have hdescent : baseEnd_2556549 < baseStart_2556549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556616 : List Nat := [2, 1, 3, 1, 2, 3, 2, 2, 3, 4]
def baseStart_2556616 : Nat := 118140960795 + 2556616 * 2 ^ 59
def prefixEnd_2556616 : Nat := 4983230072969 + 3 ^ 40 * 2556616 * 2
def baseEnd_2556616 : Nat := 437590952325091487280781

theorem tailTrace_2556616 : CollatzResearch.WordTrace tailWord_2556616 prefixEnd_2556616 437590952325091487280781 := by
  unfold tailWord_2556616
  simp only [CollatzResearch.WordTrace]
  refine ⟨46623723052912171047800851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62164964070549561397067801 46623723052912171047800851)
  ·
    refine ⟨69935584579368256571701277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46623723052912171047800851 69935584579368256571701277)
    ·
      refine ⟨26225844217263096214387979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69935584579368256571701277 26225844217263096214387979)
      ·
        refine ⟨39338766325894644321581969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26225844217263096214387979 39338766325894644321581969)
        ·
          refine ⟨29504074744420983241186477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39338766325894644321581969 29504074744420983241186477)
          ·
            refine ⟨11064028029157868715444929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29504074744420983241186477 11064028029157868715444929)
            ·
              refine ⟨8298021021868401536583697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11064028029157868715444929 8298021021868401536583697)
              ·
                refine ⟨6223515766401301152437773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8298021021868401536583697 6223515766401301152437773)
                ·
                  refine ⟨2333818412400487932164165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6223515766401301152437773 2333818412400487932164165)
                  ·
                    refine ⟨437590952325091487280781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2333818412400487932164165 437590952325091487280781)
                    ·
                      rfl

theorem cell23_2556616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_2556616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556616 prefixEnd_2556616 := by exact prefixLift 2556616
  have htrace : WordTrace (prefixWord ++ tailWord_2556616) baseStart_2556616 baseEnd_2556616 := by
    simpa [prefixWord, tailWord_2556616, baseEnd_2556616] using wordTrace_append hprefix tailTrace_2556616
  have hstable : (prefixWord ++ tailWord_2556616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556616).length < 2 ^ (prefixWord ++ tailWord_2556616).sum := by decide
  have hdescent : baseEnd_2556616 < baseStart_2556616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556643 : List Nat := [1, 1, 1, 7, 1, 2, 1, 2, 2, 2, 3]
def baseStart_2556643 : Nat := 118140960795 + 2556643 * 2 ^ 59
def prefixEnd_2556643 : Nat := 4983230072969 + 3 ^ 40 * 2556643 * 2
def baseEnd_2556643 : Nat := 1312786720952945856204719

theorem tailTrace_2556643 : CollatzResearch.WordTrace tailWord_2556643 prefixEnd_2556643 1312786720952945856204719 := by
  unfold tailWord_2556643
  simp only [CollatzResearch.WordTrace]
  refine ⟨93248430876726525706834583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62165620584484350471223055 93248430876726525706834583)
  ·
    refine ⟨139872646315089788560251875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93248430876726525706834583 139872646315089788560251875)
    ·
      refine ⟨209808969472634682840377813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139872646315089788560251875 209808969472634682840377813)
      ·
        refine ⟨4917397722014875379071355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 209808969472634682840377813 4917397722014875379071355)
        ·
          refine ⟨7376096583022313068607033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4917397722014875379071355 7376096583022313068607033)
          ·
            refine ⟨5532072437266734801455275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7376096583022313068607033 5532072437266734801455275)
            ·
              refine ⟨8298108655900102202182913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5532072437266734801455275 8298108655900102202182913)
              ·
                refine ⟨6223581491925076651637185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8298108655900102202182913 6223581491925076651637185)
                ·
                  refine ⟨4667686118943807488727889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6223581491925076651637185 4667686118943807488727889)
                  ·
                    refine ⟨3500764589207855616545917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4667686118943807488727889 3500764589207855616545917)
                    ·
                      refine ⟨1312786720952945856204719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3500764589207855616545917 1312786720952945856204719)
                      ·
                        rfl

theorem cell23_2556643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_2556643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556643 prefixEnd_2556643 := by exact prefixLift 2556643
  have htrace : WordTrace (prefixWord ++ tailWord_2556643) baseStart_2556643 baseEnd_2556643 := by
    simpa [prefixWord, tailWord_2556643, baseEnd_2556643] using wordTrace_append hprefix tailTrace_2556643
  have hstable : (prefixWord ++ tailWord_2556643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556643).length < 2 ^ (prefixWord ++ tailWord_2556643).sum := by decide
  have hdescent : baseEnd_2556643 < baseStart_2556643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556659 : List Nat := [1, 1, 1, 2, 2, 3, 1, 4, 3, 5]
def baseStart_2556659 : Nat := 118140960795 + 2556659 * 2 ^ 59
def prefixEnd_2556659 : Nat := 4983230072969 + 3 ^ 40 * 2556659 * 2
def baseEnd_2556659 : Nat := 437598312214472597868215

theorem tailTrace_2556659 : CollatzResearch.WordTrace tailWord_2556659 prefixEnd_2556659 437598312214472597868215 := by
  unfold tailWord_2556659
  simp only [CollatzResearch.WordTrace]
  refine ⟨93249014444668560439417031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62166009629779040292944687 93249014444668560439417031)
  ·
    refine ⟨139873521667002840659125547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93249014444668560439417031 139873521667002840659125547)
    ·
      refine ⟨209810282500504260988688321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139873521667002840659125547 209810282500504260988688321)
      ·
        refine ⟨157357711875378195741516241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209810282500504260988688321 157357711875378195741516241)
        ·
          refine ⟨118018283906533646806137181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157357711875378195741516241 118018283906533646806137181)
          ·
            refine ⟨44256856464950117552301443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118018283906533646806137181 44256856464950117552301443)
            ·
              refine ⟨66385284697425176328452165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44256856464950117552301443 66385284697425176328452165)
              ·
                refine ⟨12447240880767220561584781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66385284697425176328452165 12447240880767220561584781)
                ·
                  refine ⟨4667715330287707710594293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12447240880767220561584781 4667715330287707710594293)
                  ·
                    refine ⟨437598312214472597868215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4667715330287707710594293 437598312214472597868215)
                    ·
                      rfl

theorem cell23_2556659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 5].length) (baseStart_2556659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556659 prefixEnd_2556659 := by exact prefixLift 2556659
  have htrace : WordTrace (prefixWord ++ tailWord_2556659) baseStart_2556659 baseEnd_2556659 := by
    simpa [prefixWord, tailWord_2556659, baseEnd_2556659] using wordTrace_append hprefix tailTrace_2556659
  have hstable : (prefixWord ++ tailWord_2556659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556659).length < 2 ^ (prefixWord ++ tailWord_2556659).sum := by decide
  have hdescent : baseEnd_2556659 < baseStart_2556659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556666 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2]
def baseStart_2556666 : Nat := 118140960795 + 2556666 * 2 ^ 59
def prefixEnd_2556666 : Nat := 4983230072969 + 3 ^ 40 * 2556666 * 2
def baseEnd_2556666 : Nat := 1312798531007999266217113

theorem tailTrace_2556666 : CollatzResearch.WordTrace tailWord_2556666 prefixEnd_2556666 1312798531007999266217113 := by
  unfold tailWord_2556666
  simp only [CollatzResearch.WordTrace]
  refine ⟨23312317438910800158730463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62166179837095467089947901 23312317438910800158730463)
  ·
    refine ⟨34968476158366200238095695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23312317438910800158730463 34968476158366200238095695)
    ·
      refine ⟨52452714237549300357143543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34968476158366200238095695 52452714237549300357143543)
      ·
        refine ⟨78679071356323950535715315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52452714237549300357143543 78679071356323950535715315)
        ·
          refine ⟨118018607034485925803572973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78679071356323950535715315 118018607034485925803572973)
          ·
            refine ⟨44256977637932222176339865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118018607034485925803572973 44256977637932222176339865)
            ·
              refine ⟨33192733228449166632254899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44256977637932222176339865 33192733228449166632254899)
              ·
                refine ⟨49789099842673749948382349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33192733228449166632254899 49789099842673749948382349)
                ·
                  refine ⟨18670912441002656230643381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49789099842673749948382349 18670912441002656230643381)
                  ·
                    refine ⟨1750398041343999021622817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18670912441002656230643381 1750398041343999021622817)
                    ·
                      refine ⟨1312798531007999266217113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1750398041343999021622817 1312798531007999266217113)
                      ·
                        rfl

theorem cell23_2556666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2].length) (baseStart_2556666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556666 prefixEnd_2556666 := by exact prefixLift 2556666
  have htrace : WordTrace (prefixWord ++ tailWord_2556666) baseStart_2556666 baseEnd_2556666 := by
    simpa [prefixWord, tailWord_2556666, baseEnd_2556666] using wordTrace_append hprefix tailTrace_2556666
  have hstable : (prefixWord ++ tailWord_2556666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556666).length < 2 ^ (prefixWord ++ tailWord_2556666).sum := by decide
  have hdescent : baseEnd_2556666 < baseStart_2556666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556676 : List Nat := [2, 3, 2, 2, 1, 1, 3, 1, 3, 5]
def baseStart_2556676 : Nat := 118140960795 + 2556676 * 2 ^ 59
def prefixEnd_2556676 : Nat := 4983230072969 + 3 ^ 40 * 2556676 * 2
def baseEnd_2556676 : Nat := 437601221938181409030689

theorem tailTrace_2556676 : CollatzResearch.WordTrace tailWord_2556676 prefixEnd_2556676 437601221938181409030689 := by
  unfold tailWord_2556676
  simp only [CollatzResearch.WordTrace]
  refine ⟨46624817242803486171392941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62166422990404648228523921 46624817242803486171392941)
  ·
    refine ⟨17484306466051307314272353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46624817242803486171392941 17484306466051307314272353)
    ·
      refine ⟨13113229849538480485704265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17484306466051307314272353 13113229849538480485704265)
      ·
        refine ⟨9834922387153860364278199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13113229849538480485704265 9834922387153860364278199)
        ·
          refine ⟨14752383580730790546417299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9834922387153860364278199 14752383580730790546417299)
          ·
            refine ⟨22128575371096185819625949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14752383580730790546417299 22128575371096185819625949)
            ·
              refine ⟨8298215764161069682359731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22128575371096185819625949 8298215764161069682359731)
              ·
                refine ⟨12447323646241604523539597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8298215764161069682359731 12447323646241604523539597)
                ·
                  refine ⟨4667746367340601696327349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12447323646241604523539597 4667746367340601696327349)
                  ·
                    refine ⟨437601221938181409030689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4667746367340601696327349 437601221938181409030689)
                    ·
                      rfl

theorem cell23_2556676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_2556676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556676 prefixEnd_2556676 := by exact prefixLift 2556676
  have htrace : WordTrace (prefixWord ++ tailWord_2556676) baseStart_2556676 baseEnd_2556676 := by
    simpa [prefixWord, tailWord_2556676, baseEnd_2556676] using wordTrace_append hprefix tailTrace_2556676
  have hstable : (prefixWord ++ tailWord_2556676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556676).length < 2 ^ (prefixWord ++ tailWord_2556676).sum := by decide
  have hdescent : baseEnd_2556676 < baseStart_2556676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556689 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 3, 6]
def baseStart_2556689 : Nat := 118140960795 + 2556689 * 2 ^ 59
def prefixEnd_2556689 : Nat := 4983230072969 + 3 ^ 40 * 2556689 * 2
def baseEnd_2556689 : Nat := 437603447021017558743169

theorem tailTrace_2556689 : CollatzResearch.WordTrace tailWord_2556689 prefixEnd_2556689 437603447021017558743169 := by
  unfold tailWord_2556689
  simp only [CollatzResearch.WordTrace]
  refine ⟨93250108634559875563009121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62166739089706583708672747 93250108634559875563009121)
  ·
    refine ⟨69937581475919906672256841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93250108634559875563009121 69937581475919906672256841)
    ·
      refine ⟨52453186106939930004192631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69937581475919906672256841 52453186106939930004192631)
      ·
        refine ⟨78679779160409895006288947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52453186106939930004192631 78679779160409895006288947)
        ·
          refine ⟨118019668740614842509433421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78679779160409895006288947 118019668740614842509433421)
          ·
            refine ⟨44257375777730565941037533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118019668740614842509433421 44257375777730565941037533)
            ·
              refine ⟨16596515916648962227889075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44257375777730565941037533 16596515916648962227889075)
              ·
                refine ⟨24894773874973443341833613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16596515916648962227889075 24894773874973443341833613)
                ·
                  refine ⟨9335540203115041253187605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24894773874973443341833613 9335540203115041253187605)
                  ·
                    refine ⟨437603447021017558743169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9335540203115041253187605 437603447021017558743169)
                    ·
                      rfl

theorem cell23_2556689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 6].length) (baseStart_2556689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556689 prefixEnd_2556689 := by exact prefixLift 2556689
  have htrace : WordTrace (prefixWord ++ tailWord_2556689) baseStart_2556689 baseEnd_2556689 := by
    simpa [prefixWord, tailWord_2556689, baseEnd_2556689] using wordTrace_append hprefix tailTrace_2556689
  have hstable : (prefixWord ++ tailWord_2556689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556689).length < 2 ^ (prefixWord ++ tailWord_2556689).sum := by decide
  have hdescent : baseEnd_2556689 < baseStart_2556689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556693 : List Nat := [1, 3, 2, 1, 2, 2, 5, 1, 1, 5]
def baseStart_2556693 : Nat := 118140960795 + 2556693 * 2 ^ 59
def prefixEnd_2556693 : Nat := 4983230072969 + 3 ^ 40 * 2556693 * 2
def baseEnd_2556693 : Nat := 437604131661890220193163

theorem tailTrace_2556693 : CollatzResearch.WordTrace tailWord_2556693 prefixEnd_2556693 437604131661890220193163 := by
  unfold tailWord_2556693
  simp only [CollatzResearch.WordTrace]
  refine ⟨93250254526545384246154733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62166836351030256164103155 93250254526545384246154733)
  ·
    refine ⟨34968845447454519092308025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93250254526545384246154733 34968845447454519092308025)
    ·
      refine ⟨26226634085590889319231019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34968845447454519092308025 26226634085590889319231019)
      ·
        refine ⟨39339951128386333978846529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26226634085590889319231019 39339951128386333978846529)
        ·
          refine ⟨29504963346289750484134897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39339951128386333978846529 29504963346289750484134897)
          ·
            refine ⟨22128722509717312863101173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29504963346289750484134897 22128722509717312863101173)
            ·
              refine ⟨2074567735285998080915735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22128722509717312863101173 2074567735285998080915735)
              ·
                refine ⟨3111851602928997121373603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2074567735285998080915735 3111851602928997121373603)
                ·
                  refine ⟨4667777404393495682060405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3111851602928997121373603 4667777404393495682060405)
                  ·
                    refine ⟨437604131661890220193163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4667777404393495682060405 437604131661890220193163)
                    ·
                      rfl

theorem cell23_2556693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_2556693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556693 prefixEnd_2556693 := by exact prefixLift 2556693
  have htrace : WordTrace (prefixWord ++ tailWord_2556693) baseStart_2556693 baseEnd_2556693 := by
    simpa [prefixWord, tailWord_2556693, baseEnd_2556693] using wordTrace_append hprefix tailTrace_2556693
  have hstable : (prefixWord ++ tailWord_2556693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556693).length < 2 ^ (prefixWord ++ tailWord_2556693).sum := by decide
  have hdescent : baseEnd_2556693 < baseStart_2556693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556701 : List Nat := [1, 4, 2, 4, 2, 1, 2, 2, 1, 4]
def baseStart_2556701 : Nat := 118140960795 + 2556701 * 2 ^ 59
def prefixEnd_2556701 : Nat := 4983230072969 + 3 ^ 40 * 2556701 * 2
def baseEnd_2556701 : Nat := 437605500943635543093151

theorem tailTrace_2556701 : CollatzResearch.WordTrace tailWord_2556701 prefixEnd_2556701 437605500943635543093151 := by
  unfold tailWord_2556701
  simp only [CollatzResearch.WordTrace]
  refine ⟨93250546310516401612445957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62167030873677601074963971 93250546310516401612445957)
  ·
    refine ⟨17484477433221825302333617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93250546310516401612445957 17484477433221825302333617)
    ·
      refine ⟨13113358074916368976750213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17484477433221825302333617 13113358074916368976750213)
      ·
        refine ⟨2458754639046819183140665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13113358074916368976750213 2458754639046819183140665)
        ·
          refine ⟨1844065979285114387355499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2458754639046819183140665 1844065979285114387355499)
          ·
            refine ⟨2766098968927671581033249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1844065979285114387355499 2766098968927671581033249)
            ·
              refine ⟨2074574226695753685774937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2766098968927671581033249 2074574226695753685774937)
              ·
                refine ⟨1555930670021815264331203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2074574226695753685774937 1555930670021815264331203)
                ·
                  refine ⟨2333896005032722896496805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1555930670021815264331203 2333896005032722896496805)
                  ·
                    refine ⟨437605500943635543093151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2333896005032722896496805 437605500943635543093151)
                    ·
                      rfl

theorem cell23_2556701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_2556701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556701 prefixEnd_2556701 := by exact prefixLift 2556701
  have htrace : WordTrace (prefixWord ++ tailWord_2556701) baseStart_2556701 baseEnd_2556701 := by
    simpa [prefixWord, tailWord_2556701, baseEnd_2556701] using wordTrace_append hprefix tailTrace_2556701
  have hstable : (prefixWord ++ tailWord_2556701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556701).length < 2 ^ (prefixWord ++ tailWord_2556701).sum := by decide
  have hdescent : baseEnd_2556701 < baseStart_2556701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556716 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 3]
def baseStart_2556716 : Nat := 118140960795 + 2556716 * 2 ^ 59
def prefixEnd_2556716 : Nat := 4983230072969 + 3 ^ 40 * 2556716 * 2
def baseEnd_2556716 : Nat := 1312824205040724070591883

theorem tailTrace_2556716 : CollatzResearch.WordTrace tailWord_2556716 prefixEnd_2556716 1312824205040724070591883 := by
  unfold tailWord_2556716
  simp only [CollatzResearch.WordTrace]
  refine ⟨46625546702731029587121001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62167395603641372782828001 46625546702731029587121001)
  ·
    refine ⟨34969160027048272190340751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46625546702731029587121001 34969160027048272190340751)
    ·
      refine ⟨52453740040572408285511127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34969160027048272190340751 52453740040572408285511127)
      ·
        refine ⟨78680610060858612428266691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52453740040572408285511127 78680610060858612428266691)
        ·
          refine ⟨118020915091287918642400037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78680610060858612428266691 118020915091287918642400037)
          ·
            refine ⟨22128921579616484745450007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118020915091287918642400037 22128921579616484745450007)
            ·
              refine ⟨33193382369424727118175011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22128921579616484745450007 33193382369424727118175011)
              ·
                refine ⟨49790073554137090677262517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33193382369424727118175011 49790073554137090677262517)
                ·
                  refine ⟨4667819395700352250993361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49790073554137090677262517 4667819395700352250993361)
                  ·
                    refine ⟨3500864546775264188245021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4667819395700352250993361 3500864546775264188245021)
                    ·
                      refine ⟨1312824205040724070591883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3500864546775264188245021 1312824205040724070591883)
                      ·
                        rfl

theorem cell23_2556716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 3].length) (baseStart_2556716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556716 prefixEnd_2556716 := by exact prefixLift 2556716
  have htrace : WordTrace (prefixWord ++ tailWord_2556716) baseStart_2556716 baseEnd_2556716 := by
    simpa [prefixWord, tailWord_2556716, baseEnd_2556716] using wordTrace_append hprefix tailTrace_2556716
  have hstable : (prefixWord ++ tailWord_2556716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556716).length < 2 ^ (prefixWord ++ tailWord_2556716).sum := by decide
  have hdescent : baseEnd_2556716 < baseStart_2556716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556723 : List Nat := [1, 1, 1, 2, 6, 1, 2, 3, 2, 4]
def baseStart_2556723 : Nat := 118140960795 + 2556723 * 2 ^ 59
def prefixEnd_2556723 : Nat := 4983230072969 + 3 ^ 40 * 2556723 * 2
def baseEnd_2556723 : Nat := 437609266468435181068117

theorem tailTrace_2556723 : CollatzResearch.WordTrace tailWord_2556723 prefixEnd_2556723 437609266468435181068117 := by
  unfold tailWord_2556723
  simp only [CollatzResearch.WordTrace]
  refine ⟨93251348716436699369746823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62167565810957799579831215 93251348716436699369746823)
  ·
    refine ⟨139877023074655049054620235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93251348716436699369746823 139877023074655049054620235)
    ·
      refine ⟨209815534611982573581930353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139877023074655049054620235 209815534611982573581930353)
      ·
        refine ⟨157361650958986930186447765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209815534611982573581930353 157361650958986930186447765)
        ·
          refine ⟨7376327388702512352489739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 157361650958986930186447765 7376327388702512352489739)
          ·
            refine ⟨11064491083053768528734609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7376327388702512352489739 11064491083053768528734609)
            ·
              refine ⟨8298368312290326396550957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11064491083053768528734609 8298368312290326396550957)
              ·
                refine ⟨3111888117108872398706609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8298368312290326396550957 3111888117108872398706609)
                ·
                  refine ⟨2333916087831654299029957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3111888117108872398706609 2333916087831654299029957)
                  ·
                    refine ⟨437609266468435181068117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2333916087831654299029957 437609266468435181068117)
                    ·
                      rfl

theorem cell23_2556723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2, 4].length) (baseStart_2556723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556723 prefixEnd_2556723 := by exact prefixLift 2556723
  have htrace : WordTrace (prefixWord ++ tailWord_2556723) baseStart_2556723 baseEnd_2556723 := by
    simpa [prefixWord, tailWord_2556723, baseEnd_2556723] using wordTrace_append hprefix tailTrace_2556723
  have hstable : (prefixWord ++ tailWord_2556723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556723).length < 2 ^ (prefixWord ++ tailWord_2556723).sum := by decide
  have hdescent : baseEnd_2556723 < baseStart_2556723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556734 : List Nat := [4, 2, 1, 2, 4, 1, 1, 1, 2, 3, 2]
def baseStart_2556734 : Nat := 118140960795 + 2556734 * 2 ^ 59
def prefixEnd_2556734 : Nat := 4983230072969 + 3 ^ 40 * 2556734 * 2
def baseEnd_2556734 : Nat := 1312833447692505000166801

theorem tailTrace_2556734 : CollatzResearch.WordTrace tailWord_2556734 prefixEnd_2556734 1312833447692505000166801 := by
  unfold tailWord_2556734
  simp only [CollatzResearch.WordTrace]
  refine ⟨11656468739924606031049657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62167833279597898832264837 11656468739924606031049657)
  ·
    refine ⟨8742351554943454523287243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11656468739924606031049657 8742351554943454523287243)
    ·
      refine ⟨13113527332415181784930865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8742351554943454523287243 13113527332415181784930865)
      ·
        refine ⟨9835145499311386338698149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13113527332415181784930865 9835145499311386338698149)
        ·
          refine ⟨1844089781120884938505903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9835145499311386338698149 1844089781120884938505903)
          ·
            refine ⟨2766134671681327407758855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1844089781120884938505903 2766134671681327407758855)
            ·
              refine ⟨4149202007521991111638283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2766134671681327407758855 4149202007521991111638283)
              ·
                refine ⟨6223803011282986667457425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4149202007521991111638283 6223803011282986667457425)
                ·
                  refine ⟨4667852258462240000593069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6223803011282986667457425 4667852258462240000593069)
                  ·
                    refine ⟨1750444596923340000222401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4667852258462240000593069 1750444596923340000222401)
                    ·
                      refine ⟨1312833447692505000166801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1750444596923340000222401 1312833447692505000166801)
                      ·
                        rfl

theorem cell23_2556734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_2556734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556734 prefixEnd_2556734 := by exact prefixLift 2556734
  have htrace : WordTrace (prefixWord ++ tailWord_2556734) baseStart_2556734 baseEnd_2556734 := by
    simpa [prefixWord, tailWord_2556734, baseEnd_2556734] using wordTrace_append hprefix tailTrace_2556734
  have hstable : (prefixWord ++ tailWord_2556734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556734).length < 2 ^ (prefixWord ++ tailWord_2556734).sum := by decide
  have hdescent : baseEnd_2556734 < baseStart_2556734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556746 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 3, 3, 3]
def baseStart_2556746 : Nat := 118140960795 + 2556746 * 2 ^ 59
def prefixEnd_2556746 : Nat := 4983230072969 + 3 ^ 40 * 2556746 * 2
def baseEnd_2556746 : Nat := 1312839609460358953216745

theorem tailTrace_2556746 : CollatzResearch.WordTrace tailWord_2556746 prefixEnd_2556746 1312839609460358953216745 := by
  unfold tailWord_2556746
  simp only [CollatzResearch.WordTrace]
  refine ⟨23313046898838343574458523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62168125063568916198556061 23313046898838343574458523)
  ·
    refine ⟨34969570348257515361687785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23313046898838343574458523 34969570348257515361687785)
    ·
      refine ⟨26227177761193136521265839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34969570348257515361687785 26227177761193136521265839)
      ·
        refine ⟨39340766641789704781898759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26227177761193136521265839 39340766641789704781898759)
        ·
          refine ⟨59011149962684557172848139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39340766641789704781898759 59011149962684557172848139)
          ·
            refine ⟨88516724944026835759272209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59011149962684557172848139 88516724944026835759272209)
            ·
              refine ⟨66387543708020126819454157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88516724944026835759272209 66387543708020126819454157)
              ·
                refine ⟨24895328890507547557295309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66387543708020126819454157 24895328890507547557295309)
                ·
                  refine ⟨9335748333940330333985741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24895328890507547557295309 9335748333940330333985741)
                  ·
                    refine ⟨3500905625227623875244653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9335748333940330333985741 3500905625227623875244653)
                    ·
                      refine ⟨1312839609460358953216745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3500905625227623875244653 1312839609460358953216745)
                      ·
                        rfl

theorem cell23_2556746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_2556746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556746 prefixEnd_2556746 := by exact prefixLift 2556746
  have htrace : WordTrace (prefixWord ++ tailWord_2556746) baseStart_2556746 baseEnd_2556746 := by
    simpa [prefixWord, tailWord_2556746, baseEnd_2556746] using wordTrace_append hprefix tailTrace_2556746
  have hstable : (prefixWord ++ tailWord_2556746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556746).length < 2 ^ (prefixWord ++ tailWord_2556746).sum := by decide
  have hdescent : baseEnd_2556746 < baseStart_2556746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556764 : List Nat := [2, 2, 4, 2, 1, 1, 2, 4, 1, 2, 2]
def baseStart_2556764 : Nat := 118140960795 + 2556764 * 2 ^ 59
def prefixEnd_2556764 : Nat := 4983230072969 + 3 ^ 40 * 2556764 * 2
def baseEnd_2556764 : Nat := 1312848852112139882791663

theorem tailTrace_2556764 : CollatzResearch.WordTrace tailWord_2556764 prefixEnd_2556764 1312848852112139882791663 := by
  unfold tailWord_2556764
  simp only [CollatzResearch.WordTrace]
  refine ⟨46626422054644081685994673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62168562739525442247992897 46626422054644081685994673)
  ·
    refine ⟨34969816540983061264496005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46626422054644081685994673 34969816540983061264496005)
    ·
      refine ⟨6556840601434323987093001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34969816540983061264496005 6556840601434323987093001)
      ·
        refine ⟨4917630451075742990319751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6556840601434323987093001 4917630451075742990319751)
        ·
          refine ⟨7376445676613614485479627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4917630451075742990319751 7376445676613614485479627)
          ·
            refine ⟨11064668514920421728219441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7376445676613614485479627 11064668514920421728219441)
            ·
              refine ⟨8298501386190316296164581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11064668514920421728219441 8298501386190316296164581)
              ·
                refine ⟨1555969009910684305530859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8298501386190316296164581 1555969009910684305530859)
                ·
                  refine ⟨2333953514866026458296289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1555969009910684305530859 2333953514866026458296289)
                  ·
                    refine ⟨1750465136149519843722217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2333953514866026458296289 1750465136149519843722217)
                    ·
                      refine ⟨1312848852112139882791663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1750465136149519843722217 1312848852112139882791663)
                      ·
                        rfl

theorem cell23_2556764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_2556764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556764 prefixEnd_2556764 := by exact prefixLift 2556764
  have htrace : WordTrace (prefixWord ++ tailWord_2556764) baseStart_2556764 baseEnd_2556764 := by
    simpa [prefixWord, tailWord_2556764, baseEnd_2556764] using wordTrace_append hprefix tailTrace_2556764
  have hstable : (prefixWord ++ tailWord_2556764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556764).length < 2 ^ (prefixWord ++ tailWord_2556764).sum := by decide
  have hdescent : baseEnd_2556764 < baseStart_2556764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556773 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 5, 3, 2]
def baseStart_2556773 : Nat := 118140960795 + 2556773 * 2 ^ 59
def prefixEnd_2556773 : Nat := 4983230072969 + 3 ^ 40 * 2556773 * 2
def baseEnd_2556773 : Nat := 1312853473438030347579121

theorem tailTrace_2556773 : CollatzResearch.WordTrace tailWord_2556773 prefixEnd_2556773 1312853473438030347579121 := by
  unfold tailWord_2556773
  simp only [CollatzResearch.WordTrace]
  refine ⟨93253172366255557909066973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62168781577503705272711315 93253172366255557909066973)
  ·
    refine ⟨34969939637345834215900115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93253172366255557909066973 34969939637345834215900115)
    ·
      refine ⟨52454909456018751323850173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34969939637345834215900115 52454909456018751323850173)
      ·
        refine ⟨19670591046007031746443815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52454909456018751323850173 19670591046007031746443815)
        ·
          refine ⟨29505886569010547619665723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19670591046007031746443815 29505886569010547619665723)
          ·
            refine ⟨44258829853515821429498585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29505886569010547619665723 44258829853515821429498585)
            ·
              refine ⟨33194122390136866072123939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44258829853515821429498585 33194122390136866072123939)
              ·
                refine ⟨49791183585205299108185909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33194122390136866072123939 49791183585205299108185909)
                ·
                  refine ⟨4667923461112996791392429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49791183585205299108185909 4667923461112996791392429)
                  ·
                    refine ⟨1750471297917373796772161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4667923461112996791392429 1750471297917373796772161)
                    ·
                      refine ⟨1312853473438030347579121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1750471297917373796772161 1312853473438030347579121)
                      ·
                        rfl

theorem cell23_2556773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_2556773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556773 prefixEnd_2556773 := by exact prefixLift 2556773
  have htrace : WordTrace (prefixWord ++ tailWord_2556773) baseStart_2556773 baseEnd_2556773 := by
    simpa [prefixWord, tailWord_2556773, baseEnd_2556773] using wordTrace_append hprefix tailTrace_2556773
  have hstable : (prefixWord ++ tailWord_2556773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556773).length < 2 ^ (prefixWord ++ tailWord_2556773).sum := by decide
  have hdescent : baseEnd_2556773 < baseStart_2556773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556786 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 2, 3, 4]
def baseStart_2556786 : Nat := 118140960795 + 2556786 * 2 ^ 59
def prefixEnd_2556786 : Nat := 4983230072969 + 3 ^ 40 * 2556786 * 2
def baseEnd_2556786 : Nat := 1312860148686538796716561

theorem tailTrace_2556786 : CollatzResearch.WordTrace tailWord_2556786 prefixEnd_2556786 1312860148686538796716561 := by
  unfold tailWord_2556786
  simp only [CollatzResearch.WordTrace]
  refine ⟨23313411628802115282322553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62169097676805640752860141 23313411628802115282322553)
  ·
    refine ⟨17485058721601586461741915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23313411628802115282322553 17485058721601586461741915)
    ·
      refine ⟨26227588082402379692612873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17485058721601586461741915 26227588082402379692612873)
      ·
        refine ⟨19670691061801784769459655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26227588082402379692612873 19670691061801784769459655)
        ·
          refine ⟨29506036592702677154189483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19670691061801784769459655 29506036592702677154189483)
          ·
            refine ⟨44259054889054015731284225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29506036592702677154189483 44259054889054015731284225)
            ·
              refine ⟨33194291166790511798463169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44259054889054015731284225 33194291166790511798463169)
              ·
                refine ⟨24895718375092883848847377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33194291166790511798463169 24895718375092883848847377)
                ·
                  refine ⟨18671788781319662886635533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24895718375092883848847377 18671788781319662886635533)
                  ·
                    refine ⟨7001920792994873582488325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18671788781319662886635533 7001920792994873582488325)
                    ·
                      refine ⟨1312860148686538796716561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7001920792994873582488325 1312860148686538796716561)
                      ·
                        rfl

theorem cell23_2556786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_2556786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556786 prefixEnd_2556786 := by exact prefixLift 2556786
  have htrace : WordTrace (prefixWord ++ tailWord_2556786) baseStart_2556786 baseEnd_2556786 := by
    simpa [prefixWord, tailWord_2556786, baseEnd_2556786] using wordTrace_append hprefix tailTrace_2556786
  have hstable : (prefixWord ++ tailWord_2556786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556786).length < 2 ^ (prefixWord ++ tailWord_2556786).sum := by decide
  have hdescent : baseEnd_2556786 < baseStart_2556786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556798 : List Nat := [4, 2, 3, 1, 2, 2, 1, 3, 1, 2, 2]
def baseStart_2556798 : Nat := 118140960795 + 2556798 * 2 ^ 59
def prefixEnd_2556798 : Nat := 4983230072969 + 3 ^ 40 * 2556798 * 2
def baseEnd_2556798 : Nat := 1312866310454392749766507

theorem tailTrace_2556798 : CollatzResearch.WordTrace tailWord_2556798 prefixEnd_2556798 1312866310454392749766507 := by
  unfold tailWord_2556798
  simp only [CollatzResearch.WordTrace]
  refine ⟨11656760523895623397340881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62169389460776658119151365 11656760523895623397340881)
  ·
    refine ⟨8742570392921717548005661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11656760523895623397340881 8742570392921717548005661)
    ·
      refine ⟨3278463897345644080502123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8742570392921717548005661 3278463897345644080502123)
      ·
        refine ⟨4917695846018466120753185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3278463897345644080502123 4917695846018466120753185)
        ·
          refine ⟨3688271884513849590564889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4917695846018466120753185 3688271884513849590564889)
          ·
            refine ⟨2766203913385387192923667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3688271884513849590564889 2766203913385387192923667)
            ·
              refine ⟨4149305870078080789385501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2766203913385387192923667 4149305870078080789385501)
              ·
                refine ⟨1555989701279280296019563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4149305870078080789385501 1555989701279280296019563)
                ·
                  refine ⟨2333984551918920444029345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1555989701279280296019563 2333984551918920444029345)
                  ·
                    refine ⟨1750488413939190333022009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2333984551918920444029345 1750488413939190333022009)
                    ·
                      refine ⟨1312866310454392749766507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1750488413939190333022009 1312866310454392749766507)
                      ·
                        rfl

theorem cell23_2556798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_2556798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556798 prefixEnd_2556798 := by exact prefixLift 2556798
  have htrace : WordTrace (prefixWord ++ tailWord_2556798) baseStart_2556798 baseEnd_2556798 := by
    simpa [prefixWord, tailWord_2556798, baseEnd_2556798] using wordTrace_append hprefix tailTrace_2556798
  have hstable : (prefixWord ++ tailWord_2556798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556798).length < 2 ^ (prefixWord ++ tailWord_2556798).sum := by decide
  have hdescent : baseEnd_2556798 < baseStart_2556798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556803 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 3, 4, 2]
def baseStart_2556803 : Nat := 118140960795 + 2556803 * 2 ^ 59
def prefixEnd_2556803 : Nat := 4983230072969 + 3 ^ 40 * 2556803 * 2
def baseEnd_2556803 : Nat := 1312868877857665230203983

theorem tailTrace_2556803 : CollatzResearch.WordTrace tailWord_2556803 prefixEnd_2556803 1312868877857665230203983 := by
  unfold tailWord_2556803
  simp only [CollatzResearch.WordTrace]
  refine ⟨93254266556146873032659063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62169511037431248688439375 93254266556146873032659063)
  ·
    refine ⟨139881399834220309548988595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93254266556146873032659063 139881399834220309548988595)
    ·
      refine ⟨209822099751330464323482893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139881399834220309548988595 209822099751330464323482893)
      ·
        refine ⟨78683287406748924121306085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209822099751330464323482893 78683287406748924121306085)
        ·
          refine ⟨14753116388765423272744891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78683287406748924121306085 14753116388765423272744891)
          ·
            refine ⟨22129674583148134909117337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14753116388765423272744891 22129674583148134909117337)
            ·
              refine ⟨16597255937361101181838003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22129674583148134909117337 16597255937361101181838003)
              ·
                refine ⟨24895883906041651772757005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16597255937361101181838003 24895883906041651772757005)
                ·
                  refine ⟨9335956464765619414783877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24895883906041651772757005 9335956464765619414783877)
                  ·
                    refine ⟨1750491837143553640271977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9335956464765619414783877 1750491837143553640271977)
                    ·
                      refine ⟨1312868877857665230203983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1750491837143553640271977 1312868877857665230203983)
                      ·
                        rfl

theorem cell23_2556803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 4, 2].length) (baseStart_2556803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556803 prefixEnd_2556803 := by exact prefixLift 2556803
  have htrace : WordTrace (prefixWord ++ tailWord_2556803) baseStart_2556803 baseEnd_2556803 := by
    simpa [prefixWord, tailWord_2556803, baseEnd_2556803] using wordTrace_append hprefix tailTrace_2556803
  have hstable : (prefixWord ++ tailWord_2556803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556803).length < 2 ^ (prefixWord ++ tailWord_2556803).sum := by decide
  have hdescent : baseEnd_2556803 < baseStart_2556803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556910 : List Nat := [4, 1, 2, 1, 4, 1, 1, 1, 1, 3, 4]
def baseStart_2556910 : Nat := 118140960795 + 2556910 * 2 ^ 59
def prefixEnd_2556910 : Nat := 4983230072969 + 3 ^ 40 * 2556910 * 2
def baseEnd_2556910 : Nat := 1312923820287696311565991

theorem tailTrace_2556910 : CollatzResearch.WordTrace tailWord_2556910 prefixEnd_2556910 1312923820287696311565991 := by
  unfold tailWord_2556910
  simp only [CollatzResearch.WordTrace]
  refine ⟨11657271145844903788350523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62172112777839486871202789 11657271145844903788350523)
  ·
    refine ⟨17485906718767355682525785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11657271145844903788350523 17485906718767355682525785)
    ·
      refine ⟨13114430039075516761894339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17485906718767355682525785 13114430039075516761894339)
      ·
        refine ⟨19671645058613275142841509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13114430039075516761894339 19671645058613275142841509)
        ·
          refine ⟨3688433448489989089282783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19671645058613275142841509 3688433448489989089282783)
          ·
            refine ⟨5532650172734983633924175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3688433448489989089282783 5532650172734983633924175)
            ·
              refine ⟨8298975259102475450886263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5532650172734983633924175 8298975259102475450886263)
              ·
                refine ⟨12448462888653713176329395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8298975259102475450886263 12448462888653713176329395)
                ·
                  refine ⟨18672694332980569764494093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12448462888653713176329395 18672694332980569764494093)
                  ·
                    refine ⟨7002260374867713661685285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18672694332980569764494093 7002260374867713661685285)
                    ·
                      refine ⟨1312923820287696311565991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7002260374867713661685285 1312923820287696311565991)
                      ·
                        rfl

theorem cell23_2556910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_2556910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556910 prefixEnd_2556910 := by exact prefixLift 2556910
  have htrace : WordTrace (prefixWord ++ tailWord_2556910) baseStart_2556910 baseEnd_2556910 := by
    simpa [prefixWord, tailWord_2556910, baseEnd_2556910] using wordTrace_append hprefix tailTrace_2556910
  have hstable : (prefixWord ++ tailWord_2556910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556910).length < 2 ^ (prefixWord ++ tailWord_2556910).sum := by decide
  have hdescent : baseEnd_2556910 < baseStart_2556910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2556983 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 4]
def baseStart_2556983 : Nat := 118140960795 + 2556983 * 2 ^ 59
def prefixEnd_2556983 : Nat := 4983230072969 + 3 ^ 40 * 2556983 * 2
def baseEnd_2556983 : Nat := 1312961304375474525953155

theorem tailTrace_2556983 : CollatzResearch.WordTrace tailWord_2556983 prefixEnd_2556983 1312961304375474525953155 := by
  unfold tailWord_2556983
  simp only [CollatzResearch.WordTrace]
  refine ⟨93260831695494763774211603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62173887796996509182807735 93260831695494763774211603)
  ·
    refine ⟨139891247543242145661317405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93260831695494763774211603 139891247543242145661317405)
    ·
      refine ⟨52459217828715804622994027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139891247543242145661317405 52459217828715804622994027)
      ·
        refine ⟨78688826743073706934491041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52459217828715804622994027 78688826743073706934491041)
        ·
          refine ⟨59016620057305280200868281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78688826743073706934491041 59016620057305280200868281)
          ·
            refine ⟨44262465042978960150651211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59016620057305280200868281 44262465042978960150651211)
            ·
              refine ⟨66393697564468440225976817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44262465042978960150651211 66393697564468440225976817)
              ·
                refine ⟨49795273173351330169482613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66393697564468440225976817 49795273173351330169482613)
                ·
                  refine ⟨4668306860001687203388995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49795273173351330169482613 4668306860001687203388995)
                  ·
                    refine ⟨7002460290002530805083493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4668306860001687203388995 7002460290002530805083493)
                    ·
                      refine ⟨1312961304375474525953155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7002460290002530805083493 1312961304375474525953155)
                      ·
                        rfl

theorem cell23_2556983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_2556983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2556983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2556983 prefixEnd_2556983 := by exact prefixLift 2556983
  have htrace : WordTrace (prefixWord ++ tailWord_2556983) baseStart_2556983 baseEnd_2556983 := by
    simpa [prefixWord, tailWord_2556983, baseEnd_2556983] using wordTrace_append hprefix tailTrace_2556983
  have hstable : (prefixWord ++ tailWord_2556983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2556983).length < 2 ^ (prefixWord ++ tailWord_2556983).sum := by decide
  have hdescent : baseEnd_2556983 < baseStart_2556983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2556983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557013 : List Nat := [1, 3, 2, 2, 1, 2, 1, 3, 1, 1, 6]
def baseStart_2557013 : Nat := 118140960795 + 2557013 * 2 ^ 59
def prefixEnd_2557013 : Nat := 4983230072969 + 3 ^ 40 * 2557013 * 2
def baseEnd_2557013 : Nat := 1312976708795109408578017

theorem tailTrace_2557013 : CollatzResearch.WordTrace tailWord_2557013 prefixEnd_2557013 1312976708795109408578017 := by
  unfold tailWord_2557013
  simp only [CollatzResearch.WordTrace]
  refine ⟨93261925885386078897803693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62174617256924052598535795 93261925885386078897803693)
  ·
    refine ⟨34973222207019779586676385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93261925885386078897803693 34973222207019779586676385)
    ·
      refine ⟨26229916655264834690007289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34973222207019779586676385 26229916655264834690007289)
      ·
        refine ⟨19672437491448626017505467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26229916655264834690007289 19672437491448626017505467)
        ·
          refine ⟨29508656237172939026258201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19672437491448626017505467 29508656237172939026258201)
          ·
            refine ⟨22131492177879704269693651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29508656237172939026258201 22131492177879704269693651)
            ·
              refine ⟨33197238266819556404540477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22131492177879704269693651 33197238266819556404540477)
              ·
                refine ⟨12448964350057333651702679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33197238266819556404540477 12448964350057333651702679)
                ·
                  refine ⟨18673446525086000477554019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12448964350057333651702679 18673446525086000477554019)
                  ·
                    refine ⟨28010169787629000716331029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18673446525086000477554019 28010169787629000716331029)
                    ·
                      refine ⟨1312976708795109408578017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28010169787629000716331029 1312976708795109408578017)
                      ·
                        rfl

theorem cell23_2557013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_2557013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557013 prefixEnd_2557013 := by exact prefixLift 2557013
  have htrace : WordTrace (prefixWord ++ tailWord_2557013) baseStart_2557013 baseEnd_2557013 := by
    simpa [prefixWord, tailWord_2557013, baseEnd_2557013] using wordTrace_append hprefix tailTrace_2557013
  have hstable : (prefixWord ++ tailWord_2557013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557013).length < 2 ^ (prefixWord ++ tailWord_2557013).sum := by decide
  have hdescent : baseEnd_2557013 < baseStart_2557013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557014 : List Nat := [5, 2, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_2557014 : Nat := 118140960795 + 2557014 * 2 ^ 59
def prefixEnd_2557014 : Nat := 4983230072969 + 3 ^ 40 * 2557014 * 2
def baseEnd_2557014 : Nat := 437659074091921301555171

theorem tailTrace_2557014 : CollatzResearch.WordTrace tailWord_2557014 prefixEnd_2557014 437659074091921301555171 := by
  unfold tailWord_2557014
  simp only [CollatzResearch.WordTrace]
  refine ⟨5828872647398903504286881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62174641572254970712393397 5828872647398903504286881)
  ·
    refine ⟨4371654485549177628215161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5828872647398903504286881 4371654485549177628215161)
    ·
      refine ⟨3278740864161883221161371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4371654485549177628215161 3278740864161883221161371)
      ·
        refine ⟨4918111296242824831742057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3278740864161883221161371 4918111296242824831742057)
        ·
          refine ⟨3688583472182118623806543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4918111296242824831742057 3688583472182118623806543)
          ·
            refine ⟨5532875208273177935709815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3688583472182118623806543 5532875208273177935709815)
            ·
              refine ⟨8299312812409766903564723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5532875208273177935709815 8299312812409766903564723)
              ·
                refine ⟨12448969218614650355347085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8299312812409766903564723 12448969218614650355347085)
                ·
                  refine ⟨4668363456980493883255157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12448969218614650355347085 4668363456980493883255157)
                  ·
                    refine ⟨437659074091921301555171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4668363456980493883255157 437659074091921301555171)
                    ·
                      rfl

theorem cell23_2557014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_2557014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557014 prefixEnd_2557014 := by exact prefixLift 2557014
  have htrace : WordTrace (prefixWord ++ tailWord_2557014) baseStart_2557014 baseEnd_2557014 := by
    simpa [prefixWord, tailWord_2557014, baseEnd_2557014] using wordTrace_append hprefix tailTrace_2557014
  have hstable : (prefixWord ++ tailWord_2557014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557014).length < 2 ^ (prefixWord ++ tailWord_2557014).sum := by decide
  have hdescent : baseEnd_2557014 < baseStart_2557014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557021 : List Nat := [1, 4, 4, 1, 2, 1, 2, 1, 2, 3, 2]
def baseStart_2557021 : Nat := 118140960795 + 2557021 * 2 ^ 59
def prefixEnd_2557021 : Nat := 4983230072969 + 3 ^ 40 * 2557021 * 2
def baseEnd_2557021 : Nat := 1312980816640345377277981

theorem tailTrace_2557021 : CollatzResearch.WordTrace tailWord_2557021 prefixEnd_2557021 1312980816640345377277981 := by
  unfold tailWord_2557021
  simp only [CollatzResearch.WordTrace]
  refine ⟨93262217669357096264094917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62174811779571397509396611 93262217669357096264094917)
  ·
    refine ⟨17486665813004455549517797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93262217669357096264094917 17486665813004455549517797)
    ·
      refine ⟨3278749839938335415534587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17486665813004455549517797 3278749839938335415534587)
      ·
        refine ⟨4918124759907503123301881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3278749839938335415534587 4918124759907503123301881)
        ·
          refine ⟨3688593569930627342476411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4918124759907503123301881 3688593569930627342476411)
          ·
            refine ⟨5532890354895941013714617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3688593569930627342476411 5532890354895941013714617)
            ·
              refine ⟨4149667766171955760285963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5532890354895941013714617 4149667766171955760285963)
              ·
                refine ⟨6224501649257933640428945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4149667766171955760285963 6224501649257933640428945)
                ·
                  refine ⟨4668376236943450230321709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6224501649257933640428945 4668376236943450230321709)
                  ·
                    refine ⟨1750641088853793836370641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4668376236943450230321709 1750641088853793836370641)
                    ·
                      refine ⟨1312980816640345377277981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1750641088853793836370641 1312980816640345377277981)
                      ·
                        rfl

theorem cell23_2557021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_2557021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557021 prefixEnd_2557021 := by exact prefixLift 2557021
  have htrace : WordTrace (prefixWord ++ tailWord_2557021) baseStart_2557021 baseEnd_2557021 := by
    simpa [prefixWord, tailWord_2557021, baseEnd_2557021] using wordTrace_append hprefix tailTrace_2557021
  have hstable : (prefixWord ++ tailWord_2557021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557021).length < 2 ^ (prefixWord ++ tailWord_2557021).sum := by decide
  have hdescent : baseEnd_2557021 < baseStart_2557021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557034 : List Nat := [3, 1, 3, 2, 2, 2, 3, 1, 1, 1, 4]
def baseStart_2557034 : Nat := 118140960795 + 2557034 * 2 ^ 59
def prefixEnd_2557034 : Nat := 4983230072969 + 3 ^ 40 * 2557034 * 2
def baseEnd_2557034 : Nat := 1312987491888853826415421

theorem tailTrace_2557034 : CollatzResearch.WordTrace tailWord_2557034 prefixEnd_2557034 1312987491888853826415421 := by
  unfold tailWord_2557034
  simp only [CollatzResearch.WordTrace]
  refine ⟨23315672954577499871079539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62175127878873332989545437 23315672954577499871079539)
  ·
    refine ⟨34973509431866249806619309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23315672954577499871079539 34973509431866249806619309)
    ·
      refine ⟨13115066036949843677482241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34973509431866249806619309 13115066036949843677482241)
      ·
        refine ⟨9836299527712382758111681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13115066036949843677482241 9836299527712382758111681)
        ·
          refine ⟨7377224645784287068583761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9836299527712382758111681 7377224645784287068583761)
          ·
            refine ⟨5532918484338215301437821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7377224645784287068583761 5532918484338215301437821)
            ·
              refine ⟨2074844431626830738039183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5532918484338215301437821 2074844431626830738039183)
              ·
                refine ⟨3112266647440246107058775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2074844431626830738039183 3112266647440246107058775)
                ·
                  refine ⟨4668399971160369160588163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3112266647440246107058775 4668399971160369160588163)
                  ·
                    refine ⟨7002599956740553740882245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4668399971160369160588163 7002599956740553740882245)
                    ·
                      refine ⟨1312987491888853826415421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7002599956740553740882245 1312987491888853826415421)
                      ·
                        rfl

theorem cell23_2557034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_2557034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557034 prefixEnd_2557034 := by exact prefixLift 2557034
  have htrace : WordTrace (prefixWord ++ tailWord_2557034) baseStart_2557034 baseEnd_2557034 := by
    simpa [prefixWord, tailWord_2557034, baseEnd_2557034] using wordTrace_append hprefix tailTrace_2557034
  have hstable : (prefixWord ++ tailWord_2557034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557034).length < 2 ^ (prefixWord ++ tailWord_2557034).sum := by decide
  have hdescent : baseEnd_2557034 < baseStart_2557034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557037 : List Nat := [1, 5, 1, 1, 2, 4, 1, 1, 1, 1, 5]
def baseStart_2557037 : Nat := 118140960795 + 2557037 * 2 ^ 59
def prefixEnd_2557037 : Nat := 4983230072969 + 3 ^ 40 * 2557037 * 2
def baseEnd_2557037 : Nat := 1312989032330817314677907

theorem tailTrace_2557037 : CollatzResearch.WordTrace tailWord_2557037 prefixEnd_2557037 1312989032330817314677907 := by
  unfold tailWord_2557037
  simp only [CollatzResearch.WordTrace]
  refine ⟨93262801237299130996677365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62175200824866087331118243 93262801237299130996677365)
  ·
    refine ⟨8743387615996793530938503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93262801237299130996677365 8743387615996793530938503)
    ·
      refine ⟨13115081423995190296407755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8743387615996793530938503 13115081423995190296407755)
      ·
        refine ⟨19672622135992785444611633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13115081423995190296407755 19672622135992785444611633)
        ·
          refine ⟨14754466601994589083458725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19672622135992785444611633 14754466601994589083458725)
          ·
            refine ⟨2766462487873985453148511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14754466601994589083458725 2766462487873985453148511)
            ·
              refine ⟨4149693731810978179722767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2766462487873985453148511 4149693731810978179722767)
              ·
                refine ⟨6224540597716467269584151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4149693731810978179722767 6224540597716467269584151)
                ·
                  refine ⟨9336810896574700904376227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6224540597716467269584151 9336810896574700904376227)
                  ·
                    refine ⟨14005216344862051356564341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9336810896574700904376227 14005216344862051356564341)
                    ·
                      refine ⟨1312989032330817314677907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14005216344862051356564341 1312989032330817314677907)
                      ·
                        rfl

theorem cell23_2557037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_2557037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557037 prefixEnd_2557037 := by exact prefixLift 2557037
  have htrace : WordTrace (prefixWord ++ tailWord_2557037) baseStart_2557037 baseEnd_2557037 := by
    simpa [prefixWord, tailWord_2557037, baseEnd_2557037] using wordTrace_append hprefix tailTrace_2557037
  have hstable : (prefixWord ++ tailWord_2557037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557037).length < 2 ^ (prefixWord ++ tailWord_2557037).sum := by decide
  have hdescent : baseEnd_2557037 < baseStart_2557037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557045 : List Nat := [1, 3, 4, 3, 1, 2, 2, 2, 1, 1, 3]
def baseStart_2557045 : Nat := 118140960795 + 2557045 * 2 ^ 59
def prefixEnd_2557045 : Nat := 4983230072969 + 3 ^ 40 * 2557045 * 2
def baseEnd_2557045 : Nat := 1312993140176053283377871

theorem tailTrace_2557045 : CollatzResearch.WordTrace tailWord_2557045 prefixEnd_2557045 1312993140176053283377871 := by
  unfold tailWord_2557045
  simp only [CollatzResearch.WordTrace]
  refine ⟨93263093021270148362968589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62175395347513432241979059 93263093021270148362968589)
  ·
    refine ⟨34973659882976305636113221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93263093021270148362968589 34973659882976305636113221)
    ·
      refine ⟨6557561228058057306771229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34973659882976305636113221 6557561228058057306771229)
      ·
        refine ⟨2459085460521771490039211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6557561228058057306771229 2459085460521771490039211)
        ·
          refine ⟨3688628190782657235058817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2459085460521771490039211 3688628190782657235058817)
          ·
            refine ⟨2766471143086992926294113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3688628190782657235058817 2766471143086992926294113)
            ·
              refine ⟨2074853357315244694720585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2766471143086992926294113 2074853357315244694720585)
              ·
                refine ⟨1556140017986433521040439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2074853357315244694720585 1556140017986433521040439)
                ·
                  refine ⟨2334210026979650281560659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1556140017986433521040439 2334210026979650281560659)
                  ·
                    refine ⟨3501315040469475422340989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2334210026979650281560659 3501315040469475422340989)
                    ·
                      refine ⟨1312993140176053283377871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3501315040469475422340989 1312993140176053283377871)
                      ·
                        rfl

theorem cell23_2557045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_2557045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557045 prefixEnd_2557045 := by exact prefixLift 2557045
  have htrace : WordTrace (prefixWord ++ tailWord_2557045) baseStart_2557045 baseEnd_2557045 := by
    simpa [prefixWord, tailWord_2557045, baseEnd_2557045] using wordTrace_append hprefix tailTrace_2557045
  have hstable : (prefixWord ++ tailWord_2557045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557045).length < 2 ^ (prefixWord ++ tailWord_2557045).sum := by decide
  have hdescent : baseEnd_2557045 < baseStart_2557045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557053 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 1, 9]
def baseStart_2557053 : Nat := 118140960795 + 2557053 * 2 ^ 59
def prefixEnd_2557053 : Nat := 4983230072969 + 3 ^ 40 * 2557053 * 2
def baseEnd_2557053 : Nat := 437665749340429750692611

theorem tailTrace_2557053 : CollatzResearch.WordTrace tailWord_2557053 prefixEnd_2557053 437665749340429750692611 := by
  unfold tailWord_2557053
  simp only [CollatzResearch.WordTrace]
  refine ⟨93263384805241165729259813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62175589870160777152839875 93263384805241165729259813)
  ·
    refine ⟨17486884650982718574236215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93263384805241165729259813 17486884650982718574236215)
    ·
      refine ⟨26230326976474077861354323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17486884650982718574236215 26230326976474077861354323)
      ·
        refine ⟨39345490464711116792031485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26230326976474077861354323 39345490464711116792031485)
        ·
          refine ⟨14754558924266668797011807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39345490464711116792031485 14754558924266668797011807)
          ·
            refine ⟨22131838386400003195517711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14754558924266668797011807 22131838386400003195517711)
            ·
              refine ⟨33197757579600004793276567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22131838386400003195517711 33197757579600004793276567)
              ·
                refine ⟨49796636369400007189914851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33197757579600004793276567 49796636369400007189914851)
                ·
                  refine ⟨74694954554100010784872277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49796636369400007189914851 74694954554100010784872277)
                  ·
                    refine ⟨437665749340429750692611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 74694954554100010784872277 437665749340429750692611)
                    ·
                      rfl

theorem cell23_2557053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_2557053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557053 prefixEnd_2557053 := by exact prefixLift 2557053
  have htrace : WordTrace (prefixWord ++ tailWord_2557053) baseStart_2557053 baseEnd_2557053 := by
    simpa [prefixWord, tailWord_2557053, baseEnd_2557053] using wordTrace_append hprefix tailTrace_2557053
  have hstable : (prefixWord ++ tailWord_2557053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557053).length < 2 ^ (prefixWord ++ tailWord_2557053).sum := by decide
  have hdescent : baseEnd_2557053 < baseStart_2557053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557063 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 5]
def baseStart_2557063 : Nat := 118140960795 + 2557063 * 2 ^ 59
def prefixEnd_2557063 : Nat := 4983230072969 + 3 ^ 40 * 2557063 * 2
def baseEnd_2557063 : Nat := 1313002382827834212952787

theorem tailTrace_2557063 : CollatzResearch.WordTrace tailWord_2557063 prefixEnd_2557063 1313002382827834212952787 := by
  unfold tailWord_2557063
  simp only [CollatzResearch.WordTrace]
  refine ⟨93263749535204937437123843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62175833023469958291415895 93263749535204937437123843)
  ·
    refine ⟨139895624302807406155685765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93263749535204937437123843 139895624302807406155685765)
    ·
      refine ⟨26230429556776388654191081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139895624302807406155685765 26230429556776388654191081)
      ·
        refine ⟨19672822167582291490643311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26230429556776388654191081 19672822167582291490643311)
        ·
          refine ⟨29509233251373437235964967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19672822167582291490643311 29509233251373437235964967)
          ·
            refine ⟨44263849877060155853947451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29509233251373437235964967 44263849877060155853947451)
            ·
              refine ⟨66395774815590233780921177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44263849877060155853947451 66395774815590233780921177)
              ·
                refine ⟨49796831111692675335690883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66395774815590233780921177 49796831111692675335690883)
                ·
                  refine ⟨74695246667539013003536325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49796831111692675335690883 74695246667539013003536325)
                  ·
                    refine ⟨14005358750163564938163061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74695246667539013003536325 14005358750163564938163061)
                    ·
                      refine ⟨1313002382827834212952787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14005358750163564938163061 1313002382827834212952787)
                      ·
                        rfl

theorem cell23_2557063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_2557063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557063 prefixEnd_2557063 := by exact prefixLift 2557063
  have htrace : WordTrace (prefixWord ++ tailWord_2557063) baseStart_2557063 baseEnd_2557063 := by
    simpa [prefixWord, tailWord_2557063, baseEnd_2557063] using wordTrace_append hprefix tailTrace_2557063
  have hstable : (prefixWord ++ tailWord_2557063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557063).length < 2 ^ (prefixWord ++ tailWord_2557063).sum := by decide
  have hdescent : baseEnd_2557063 < baseStart_2557063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557130 : List Nat := [3, 1, 2, 1, 3, 2, 2, 2, 7]
def baseStart_2557130 : Nat := 118140960795 + 2557130 * 2 ^ 59
def prefixEnd_2557130 : Nat := 4983230072969 + 3 ^ 40 * 2557130 * 2
def baseEnd_2557130 : Nat := 145892976225742827868331

theorem tailTrace_2557130 : CollatzResearch.WordTrace tailWord_2557130 prefixEnd_2557130 145892976225742827868331 := by
  unfold tailWord_2557130
  simp only [CollatzResearch.WordTrace]
  refine ⟨23316548306490551969953211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62177462150641471919875229 23316548306490551969953211)
  ·
    refine ⟨34974822459735827954929817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23316548306490551969953211 34974822459735827954929817)
    ·
      refine ⟨26231116844801870966197363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34974822459735827954929817 26231116844801870966197363)
      ·
        refine ⟨39346675267202806449296045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26231116844801870966197363 39346675267202806449296045)
        ·
          refine ⟨14755003225201052418486017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39346675267202806449296045 14755003225201052418486017)
          ·
            refine ⟨11066252418900789313864513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14755003225201052418486017 11066252418900789313864513)
            ·
              refine ⟨8299689314175591985398385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11066252418900789313864513 8299689314175591985398385)
              ·
                refine ⟨6224766985631693989048789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8299689314175591985398385 6224766985631693989048789)
                ·
                  refine ⟨145892976225742827868331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6224766985631693989048789 145892976225742827868331)
                  ·
                    rfl

theorem cell23_2557130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 7].length) (baseStart_2557130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557130 prefixEnd_2557130 := by exact prefixLift 2557130
  have htrace : WordTrace (prefixWord ++ tailWord_2557130) baseStart_2557130 baseEnd_2557130 := by
    simpa [prefixWord, tailWord_2557130, baseEnd_2557130] using wordTrace_append hprefix tailTrace_2557130
  have hstable : (prefixWord ++ tailWord_2557130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557130).length < 2 ^ (prefixWord ++ tailWord_2557130).sum := by decide
  have hdescent : baseEnd_2557130 < baseStart_2557130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557164 : List Nat := [2, 2, 1, 1, 2, 5, 3, 2, 5]
def baseStart_2557164 : Nat := 118140960795 + 2557164 * 2 ^ 59
def prefixEnd_2557164 : Nat := 4983230072969 + 3 ^ 40 * 2557164 * 2
def baseEnd_2557164 : Nat := 145894916041548701976647

theorem tailTrace_2557164 : CollatzResearch.WordTrace tailWord_2557164 prefixEnd_2557164 145894916041548701976647 := by
  unfold tailWord_2557164
  simp only [CollatzResearch.WordTrace]
  refine ⟨46633716653919515843275273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62178288871892687791033697 46633716653919515843275273)
  ·
    refine ⟨34975287490439636882456455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46633716653919515843275273 34975287490439636882456455)
    ·
      refine ⟨52462931235659455323684683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34975287490439636882456455 52462931235659455323684683)
      ·
        refine ⟨78694396853489182985527025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52462931235659455323684683 78694396853489182985527025)
        ·
          refine ⟨59020797640116887239145269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78694396853489182985527025 59020797640116887239145269)
          ·
            refine ⟨5533199778760958178669869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59020797640116887239145269 5533199778760958178669869)
            ·
              refine ⟨2074949917035359317001201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5533199778760958178669869 2074949917035359317001201)
              ·
                refine ⟨1556212437776519487750901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2074949917035359317001201 1556212437776519487750901)
                ·
                  refine ⟨145894916041548701976647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1556212437776519487750901 145894916041548701976647)
                  ·
                    rfl

theorem cell23_2557164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2, 5].length) (baseStart_2557164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557164 prefixEnd_2557164 := by exact prefixLift 2557164
  have htrace : WordTrace (prefixWord ++ tailWord_2557164) baseStart_2557164 baseEnd_2557164 := by
    simpa [prefixWord, tailWord_2557164, baseEnd_2557164] using wordTrace_append hprefix tailTrace_2557164
  have hstable : (prefixWord ++ tailWord_2557164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557164).length < 2 ^ (prefixWord ++ tailWord_2557164).sum := by decide
  have hdescent : baseEnd_2557164 < baseStart_2557164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557200 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 3]
def baseStart_2557200 : Nat := 118140960795 + 2557200 * 2 ^ 59
def prefixEnd_2557200 : Nat := 4983230072969 + 3 ^ 40 * 2557200 * 2
def baseEnd_2557200 : Nat := 1313072729677500176939657

theorem tailTrace_2557200 : CollatzResearch.WordTrace tailWord_2557200 prefixEnd_2557200 1313072729677500176939657 := by
  unfold tailWord_2557200
  simp only [CollatzResearch.WordTrace]
  refine ⟨46634373167854304917430527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62179164223805739889907369 46634373167854304917430527)
  ·
    refine ⟨69951559751781457376145791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46634373167854304917430527 69951559751781457376145791)
    ·
      refine ⟨104927339627672186064218687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69951559751781457376145791 104927339627672186064218687)
      ·
        refine ⟨157391009441508279096328031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104927339627672186064218687 157391009441508279096328031)
        ·
          refine ⟨236086514162262418644492047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157391009441508279096328031 236086514162262418644492047)
          ·
            refine ⟨354129771243393627966738071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236086514162262418644492047 354129771243393627966738071)
            ·
              refine ⟨531194656865090441950107107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 354129771243393627966738071 531194656865090441950107107)
              ·
                refine ⟨796791985297635662925160661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 531194656865090441950107107 796791985297635662925160661)
                ·
                  refine ⟨18674812155413335849808453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 796791985297635662925160661 18674812155413335849808453)
                  ·
                    refine ⟨3501527279140000471839085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18674812155413335849808453 3501527279140000471839085)
                    ·
                      refine ⟨1313072729677500176939657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3501527279140000471839085 1313072729677500176939657)
                      ·
                        rfl

theorem cell23_2557200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 3].length) (baseStart_2557200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557200 prefixEnd_2557200 := by exact prefixLift 2557200
  have htrace : WordTrace (prefixWord ++ tailWord_2557200) baseStart_2557200 baseEnd_2557200 := by
    simpa [prefixWord, tailWord_2557200, baseEnd_2557200] using wordTrace_append hprefix tailTrace_2557200
  have hstable : (prefixWord ++ tailWord_2557200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557200).length < 2 ^ (prefixWord ++ tailWord_2557200).sum := by decide
  have hdescent : baseEnd_2557200 < baseStart_2557200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557237 : List Nat := [1, 3, 3, 1, 2, 2, 2, 3, 6]
def baseStart_2557237 : Nat := 118140960795 + 2557237 * 2 ^ 59
def prefixEnd_2557237 : Nat := 4983230072969 + 3 ^ 40 * 2557237 * 2
def baseEnd_2557237 : Nat := 145899080940190725797443

theorem tailTrace_2557237 : CollatzResearch.WordTrace tailWord_2557237 prefixEnd_2557237 145899080940190725797443 := by
  unfold tailWord_2557237
  simp only [CollatzResearch.WordTrace]
  refine ⟨93270095836574565153957965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62180063891049710102638643 93270095836574565153957965)
  ·
    refine ⟨34976285938715461932734237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93270095836574565153957965 34976285938715461932734237)
    ·
      refine ⟨13116107227018298224775339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34976285938715461932734237 13116107227018298224775339)
      ·
        refine ⟨19674160840527447337163009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13116107227018298224775339 19674160840527447337163009)
        ·
          refine ⟨14755620630395585502872257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19674160840527447337163009 14755620630395585502872257)
          ·
            refine ⟨11066715472796689127154193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14755620630395585502872257 11066715472796689127154193)
            ·
              refine ⟨8300036604597516845365645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11066715472796689127154193 8300036604597516845365645)
              ·
                refine ⟨3112513726724068817012117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8300036604597516845365645 3112513726724068817012117)
                ·
                  refine ⟨145899080940190725797443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3112513726724068817012117 145899080940190725797443)
                  ·
                    rfl

theorem cell23_2557237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 6].length) (baseStart_2557237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557237 prefixEnd_2557237 := by exact prefixLift 2557237
  have htrace : WordTrace (prefixWord ++ tailWord_2557237) baseStart_2557237 baseEnd_2557237 := by
    simpa [prefixWord, tailWord_2557237, baseEnd_2557237] using wordTrace_append hprefix tailTrace_2557237
  have hstable : (prefixWord ++ tailWord_2557237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557237).length < 2 ^ (prefixWord ++ tailWord_2557237).sum := by decide
  have hdescent : baseEnd_2557237 < baseStart_2557237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557267 : List Nat := [1, 1, 1, 2, 1, 1, 7, 3, 1, 5]
def baseStart_2557267 : Nat := 118140960795 + 2557267 * 2 ^ 59
def prefixEnd_2557267 : Nat := 4983230072969 + 3 ^ 40 * 2557267 * 2
def baseEnd_2557267 : Nat := 437702377627117138267283

theorem tailTrace_2557267 : CollatzResearch.WordTrace tailWord_2557267 prefixEnd_2557267 437702377627117138267283 := by
  unfold tailWord_2557267
  simp only [CollatzResearch.WordTrace]
  refine ⟨93271190026465880277550055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62180793350977253518366703 93271190026465880277550055)
  ·
    refine ⟨139906785039698820416325083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93271190026465880277550055 139906785039698820416325083)
    ·
      refine ⟨209860177559548230624487625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139906785039698820416325083 209860177559548230624487625)
      ·
        refine ⟨157395133169661172968365719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209860177559548230624487625 157395133169661172968365719)
        ·
          refine ⟨236092699754491759452548579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157395133169661172968365719 236092699754491759452548579)
          ·
            refine ⟨354139049631737639178822869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236092699754491759452548579 354139049631737639178822869)
            ·
              refine ⟨8300133975743850918253661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 354139049631737639178822869 8300133975743850918253661)
              ·
                refine ⟨3112550240903944094345123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8300133975743850918253661 3112550240903944094345123)
                ·
                  refine ⟨4668825361355916141517685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3112550240903944094345123 4668825361355916141517685)
                  ·
                    refine ⟨437702377627117138267283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4668825361355916141517685 437702377627117138267283)
                    ·
                      rfl

theorem cell23_2557267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 5].length) (baseStart_2557267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557267 prefixEnd_2557267 := by exact prefixLift 2557267
  have htrace : WordTrace (prefixWord ++ tailWord_2557267) baseStart_2557267 baseEnd_2557267 := by
    simpa [prefixWord, tailWord_2557267, baseEnd_2557267] using wordTrace_append hprefix tailTrace_2557267
  have hstable : (prefixWord ++ tailWord_2557267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557267).length < 2 ^ (prefixWord ++ tailWord_2557267).sum := by decide
  have hdescent : baseEnd_2557267 < baseStart_2557267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557274 : List Nat := [3, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2]
def baseStart_2557274 : Nat := 118140960795 + 2557274 * 2 ^ 59
def prefixEnd_2557274 : Nat := 4983230072969 + 3 ^ 40 * 2557274 * 2
def baseEnd_2557274 : Nat := 1313110727245932887414317

theorem tailTrace_2557274 : CollatzResearch.WordTrace tailWord_2557274 prefixEnd_2557274 1313110727245932887414317 := by
  unfold tailWord_2557274
  simp only [CollatzResearch.WordTrace]
  refine ⟨23317861334360130118263719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62180963558293680315369917 23317861334360130118263719)
  ·
    refine ⟨34976792001540195177395579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23317861334360130118263719 34976792001540195177395579)
    ·
      refine ⟨52465188002310292766093369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34976792001540195177395579 52465188002310292766093369)
      ·
        refine ⟨39348891001732719574570027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52465188002310292766093369 39348891001732719574570027)
        ·
          refine ⟨59023336502599079361855041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39348891001732719574570027 59023336502599079361855041)
          ·
            refine ⟨44267502376949309521391281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59023336502599079361855041 44267502376949309521391281)
            ·
              refine ⟨33200626782711982141043461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44267502376949309521391281 33200626782711982141043461)
              ·
                refine ⟨6225117521758496651445649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33200626782711982141043461 6225117521758496651445649)
                ·
                  refine ⟨4668838141318872488584237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6225117521758496651445649 4668838141318872488584237)
                  ·
                    refine ⟨1750814302994577183219089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4668838141318872488584237 1750814302994577183219089)
                    ·
                      refine ⟨1313110727245932887414317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1750814302994577183219089 1313110727245932887414317)
                      ·
                        rfl

theorem cell23_2557274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2].length) (baseStart_2557274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557274 prefixEnd_2557274 := by exact prefixLift 2557274
  have htrace : WordTrace (prefixWord ++ tailWord_2557274) baseStart_2557274 baseEnd_2557274 := by
    simpa [prefixWord, tailWord_2557274, baseEnd_2557274] using wordTrace_append hprefix tailTrace_2557274
  have hstable : (prefixWord ++ tailWord_2557274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557274).length < 2 ^ (prefixWord ++ tailWord_2557274).sum := by decide
  have hdescent : baseEnd_2557274 < baseStart_2557274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557297 : List Nat := [1, 2, 2, 2, 1, 2, 5, 1, 1, 6]
def baseStart_2557297 : Nat := 118140960795 + 2557297 * 2 ^ 59
def prefixEnd_2557297 : Nat := 4983230072969 + 3 ^ 40 * 2557297 * 2
def baseEnd_2557297 : Nat := 437707512433662099142237

theorem tailTrace_2557297 : CollatzResearch.WordTrace tailWord_2557297 prefixEnd_2557297 437707512433662099142237 := by
  unfold tailWord_2557297
  simp only [CollatzResearch.WordTrace]
  refine ⟨93272284216357195401142145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62181522810904796934094763 93272284216357195401142145)
  ·
    refine ⟨69954213162267896550856609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93272284216357195401142145 69954213162267896550856609)
    ·
      refine ⟨52465659871700922413142457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69954213162267896550856609 52465659871700922413142457)
      ·
        refine ⟨39349244903775691809856843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52465659871700922413142457 39349244903775691809856843)
        ·
          refine ⟨59023867355663537714785265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39349244903775691809856843 59023867355663537714785265)
          ·
            refine ⟨44267900516747653286088949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59023867355663537714785265 44267900516747653286088949)
            ·
              refine ⟨4150115673445092495570839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44267900516747653286088949 4150115673445092495570839)
              ·
                refine ⟨6225173510167638743356259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4150115673445092495570839 6225173510167638743356259)
                ·
                  refine ⟨9337760265251458115034389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6225173510167638743356259 9337760265251458115034389)
                  ·
                    refine ⟨437707512433662099142237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9337760265251458115034389 437707512433662099142237)
                    ·
                      rfl

theorem cell23_2557297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 6].length) (baseStart_2557297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557297 prefixEnd_2557297 := by exact prefixLift 2557297
  have htrace : WordTrace (prefixWord ++ tailWord_2557297) baseStart_2557297 baseEnd_2557297 := by
    simpa [prefixWord, tailWord_2557297, baseEnd_2557297] using wordTrace_append hprefix tailTrace_2557297
  have hstable : (prefixWord ++ tailWord_2557297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557297).length < 2 ^ (prefixWord ++ tailWord_2557297).sum := by decide
  have hdescent : baseEnd_2557297 < baseStart_2557297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557301 : List Nat := [1, 3, 4, 1, 3, 1, 2, 2, 1, 5]
def baseStart_2557301 : Nat := 118140960795 + 2557301 * 2 ^ 59
def prefixEnd_2557301 : Nat := 4983230072969 + 3 ^ 40 * 2557301 * 2
def baseEnd_2557301 : Nat := 437708197074534760592231

theorem tailTrace_2557301 : CollatzResearch.WordTrace tailWord_2557301 prefixEnd_2557301 437708197074534760592231 := by
  unfold tailWord_2557301
  simp only [CollatzResearch.WordTrace]
  refine ⟨93272430108342704084287757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62181620072228469389525171 93272430108342704084287757)
  ·
    refine ⟨34977161290628514031607909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93272430108342704084287757 34977161290628514031607909)
    ·
      refine ⟨6558217741992846380926483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34977161290628514031607909 6558217741992846380926483)
      ·
        refine ⟨9837326612989269571389725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6558217741992846380926483 9837326612989269571389725)
        ·
          refine ⟨3688997479870976089271147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9837326612989269571389725 3688997479870976089271147)
          ·
            refine ⟨5533496219806464133906721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3688997479870976089271147 5533496219806464133906721)
            ·
              refine ⟨4150122164854848100430041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5533496219806464133906721 4150122164854848100430041)
              ·
                refine ⟨3112591623641136075322531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4150122164854848100430041 3112591623641136075322531)
                ·
                  refine ⟨4668887435461704112983797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3112591623641136075322531 4668887435461704112983797)
                  ·
                    refine ⟨437708197074534760592231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4668887435461704112983797 437708197074534760592231)
                    ·
                      rfl

theorem cell23_2557301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_2557301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557301 prefixEnd_2557301 := by exact prefixLift 2557301
  have htrace : WordTrace (prefixWord ++ tailWord_2557301) baseStart_2557301 baseEnd_2557301 := by
    simpa [prefixWord, tailWord_2557301, baseEnd_2557301] using wordTrace_append hprefix tailTrace_2557301
  have hstable : (prefixWord ++ tailWord_2557301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557301).length < 2 ^ (prefixWord ++ tailWord_2557301).sum := by decide
  have hdescent : baseEnd_2557301 < baseStart_2557301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557317 : List Nat := [1, 3, 1, 1, 3, 1, 2, 4, 1, 2, 4]
def baseStart_2557317 : Nat := 118140960795 + 2557317 * 2 ^ 59
def prefixEnd_2557317 : Nat := 4983230072969 + 3 ^ 40 * 2557317 * 2
def baseEnd_2557317 : Nat := 1313132806914076219176619

theorem tailTrace_2557317 : CollatzResearch.WordTrace tailWord_2557317 prefixEnd_2557317 1313132806914076219176619 := by
  unfold tailWord_2557317
  simp only [CollatzResearch.WordTrace]
  refine ⟨93273013676284738816870205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62182009117523159211246803 93273013676284738816870205)
  ·
    refine ⟨34977380128606777056326327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93273013676284738816870205 34977380128606777056326327)
    ·
      refine ⟨52466070192910165584489491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34977380128606777056326327 52466070192910165584489491)
      ·
        refine ⟨78699105289365248376734237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52466070192910165584489491 78699105289365248376734237)
        ·
          refine ⟨29512164483511968141275339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78699105289365248376734237 29512164483511968141275339)
          ·
            refine ⟨44268246725267952211913009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29512164483511968141275339 44268246725267952211913009)
            ·
              refine ⟨33201185043950964158934757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44268246725267952211913009 33201185043950964158934757)
              ·
                refine ⟨6225222195740805779800267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33201185043950964158934757 6225222195740805779800267)
                ·
                  refine ⟨9337833293611208669700401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6225222195740805779800267 9337833293611208669700401)
                  ·
                    refine ⟨7003374970208406502275301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9337833293611208669700401 7003374970208406502275301)
                    ·
                      refine ⟨1313132806914076219176619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7003374970208406502275301 1313132806914076219176619)
                      ·
                        rfl

theorem cell23_2557317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_2557317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557317 prefixEnd_2557317 := by exact prefixLift 2557317
  have htrace : WordTrace (prefixWord ++ tailWord_2557317) baseStart_2557317 baseEnd_2557317 := by
    simpa [prefixWord, tailWord_2557317, baseEnd_2557317] using wordTrace_append hprefix tailTrace_2557317
  have hstable : (prefixWord ++ tailWord_2557317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557317).length < 2 ^ (prefixWord ++ tailWord_2557317).sum := by decide
  have hdescent : baseEnd_2557317 < baseStart_2557317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557324 : List Nat := [2, 2, 1, 2, 1, 3, 1, 5, 1, 2, 3]
def baseStart_2557324 : Nat := 118140960795 + 2557324 * 2 ^ 59
def prefixEnd_2557324 : Nat := 4983230072969 + 3 ^ 40 * 2557324 * 2
def baseEnd_2557324 : Nat := 1313136401278657691789087

theorem tailTrace_2557324 : CollatzResearch.WordTrace tailWord_2557324 prefixEnd_2557324 1313136401278657691789087 := by
  unfold tailWord_2557324
  simp only [CollatzResearch.WordTrace]
  refine ⟨46636634493629689506187513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62182179324839586008250017 46636634493629689506187513)
  ·
    refine ⟨34977475870222267129640635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46636634493629689506187513 34977475870222267129640635)
    ·
      refine ⟨52466213805333400694460953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34977475870222267129640635 52466213805333400694460953)
      ·
        refine ⟨39349660354000050520845715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52466213805333400694460953 39349660354000050520845715)
        ·
          refine ⟨59024490531000075781268573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39349660354000050520845715 59024490531000075781268573)
          ·
            refine ⟨22134183949125028417975715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59024490531000075781268573 22134183949125028417975715)
            ·
              refine ⟨33201275923687542626963573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22134183949125028417975715 33201275923687542626963573)
              ·
                refine ⟨3112619617845707121277835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33201275923687542626963573 3112619617845707121277835)
                ·
                  refine ⟨4668929426768560681916753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3112619617845707121277835 4668929426768560681916753)
                  ·
                    refine ⟨3501697070076420511437565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4668929426768560681916753 3501697070076420511437565)
                    ·
                      refine ⟨1313136401278657691789087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3501697070076420511437565 1313136401278657691789087)
                      ·
                        rfl

theorem cell23_2557324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_2557324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557324 prefixEnd_2557324 := by exact prefixLift 2557324
  have htrace : WordTrace (prefixWord ++ tailWord_2557324) baseStart_2557324 baseEnd_2557324 := by
    simpa [prefixWord, tailWord_2557324, baseEnd_2557324] using wordTrace_append hprefix tailTrace_2557324
  have hstable : (prefixWord ++ tailWord_2557324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557324).length < 2 ^ (prefixWord ++ tailWord_2557324).sum := by decide
  have hdescent : baseEnd_2557324 < baseStart_2557324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557378 : List Nat := [3, 5, 2, 1, 1, 11]
def baseStart_2557378 : Nat := 118140960795 + 2557378 * 2 ^ 59
def prefixEnd_2557378 : Nat := 4983230072969 + 3 ^ 40 * 2557378 * 2
def baseEnd_2557378 : Nat := 5403967610016462882773

theorem tailTrace_2557378 : CollatzResearch.WordTrace tailWord_2557378 prefixEnd_2557378 5403967610016462882773 := by
  unfold tailWord_2557378
  simp only [CollatzResearch.WordTrace]
  refine ⟨23318809632265936558710197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62183492352709164156560525 23318809632265936558710197)
  ·
    refine ⟨2186138403024931552379081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23318809632265936558710197 2186138403024931552379081)
    ·
      refine ⟨1639603802268698664284311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2186138403024931552379081 1639603802268698664284311)
      ·
        refine ⟨2459405703403047996426467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1639603802268698664284311 2459405703403047996426467)
        ·
          refine ⟨3689108555104571994639701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2459405703403047996426467 3689108555104571994639701)
          ·
            refine ⟨5403967610016462882773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3689108555104571994639701 5403967610016462882773)
            ·
              rfl

theorem cell23_2557378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 11].length) (baseStart_2557378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557378 prefixEnd_2557378 := by exact prefixLift 2557378
  have htrace : WordTrace (prefixWord ++ tailWord_2557378) baseStart_2557378 baseEnd_2557378 := by
    simpa [prefixWord, tailWord_2557378, baseEnd_2557378] using wordTrace_append hprefix tailTrace_2557378
  have hstable : (prefixWord ++ tailWord_2557378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557378).length < 2 ^ (prefixWord ++ tailWord_2557378).sum := by decide
  have hdescent : baseEnd_2557378 < baseStart_2557378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557388 : List Nat := [2, 2, 1, 4, 2, 2, 2, 2, 2, 1, 3]
def baseStart_2557388 : Nat := 118140960795 + 2557388 * 2 ^ 59
def prefixEnd_2557388 : Nat := 4983230072969 + 3 ^ 40 * 2557388 * 2
def baseEnd_2557388 : Nat := 1313169264040545441388793

theorem tailTrace_2557388 : CollatzResearch.WordTrace tailWord_2557388 prefixEnd_2557388 1313169264040545441388793 := by
  unfold tailWord_2557388
  simp only [CollatzResearch.WordTrace]
  refine ⟨46637801629513758971352409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62183735506018345295136545 46637801629513758971352409)
  ·
    refine ⟨34978351222135319228514307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46637801629513758971352409 34978351222135319228514307)
    ·
      refine ⟨52467526833202978842771461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34978351222135319228514307 52467526833202978842771461)
      ·
        refine ⟨9837661281225558533019649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52467526833202978842771461 9837661281225558533019649)
        ·
          refine ⟨7378245960919168899764737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9837661281225558533019649 7378245960919168899764737)
          ·
            refine ⟨5533684470689376674823553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7378245960919168899764737 5533684470689376674823553)
            ·
              refine ⟨4150263353017032506117665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5533684470689376674823553 4150263353017032506117665)
              ·
                refine ⟨3112697514762774379588249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4150263353017032506117665 3112697514762774379588249)
                ·
                  refine ⟨2334523136072080784691187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3112697514762774379588249 2334523136072080784691187)
                  ·
                    refine ⟨3501784704108121177036781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2334523136072080784691187 3501784704108121177036781)
                    ·
                      refine ⟨1313169264040545441388793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3501784704108121177036781 1313169264040545441388793)
                      ·
                        rfl

theorem cell23_2557388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_2557388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557388 prefixEnd_2557388 := by exact prefixLift 2557388
  have htrace : WordTrace (prefixWord ++ tailWord_2557388) baseStart_2557388 baseEnd_2557388 := by
    simpa [prefixWord, tailWord_2557388, baseEnd_2557388] using wordTrace_append hprefix tailTrace_2557388
  have hstable : (prefixWord ++ tailWord_2557388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557388).length < 2 ^ (prefixWord ++ tailWord_2557388).sum := by decide
  have hdescent : baseEnd_2557388 < baseStart_2557388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557398 : List Nat := [5, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2]
def baseStart_2557398 : Nat := 118140960795 + 2557398 * 2 ^ 59
def prefixEnd_2557398 : Nat := 4983230072969 + 3 ^ 40 * 2557398 * 2
def baseEnd_2557398 : Nat := 1313174398847090402263747

theorem tailTrace_2557398 : CollatzResearch.WordTrace tailWord_2557398 prefixEnd_2557398 1313174398847090402263747 := by
  unfold tailWord_2557398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5829747999311955603160553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62183978659327526433712565 5829747999311955603160553)
  ·
    refine ⟨4372310999483966702370415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5829747999311955603160553 4372310999483966702370415)
    ·
      refine ⟨6558466499225950053555623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4372310999483966702370415 6558466499225950053555623)
      ·
        refine ⟨9837699748838925080333435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6558466499225950053555623 9837699748838925080333435)
        ·
          refine ⟨14756549623258387620500153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9837699748838925080333435 14756549623258387620500153)
          ·
            refine ⟨11067412217443790715375115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14756549623258387620500153 11067412217443790715375115)
            ·
              refine ⟨16601118326165686073062673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11067412217443790715375115 16601118326165686073062673)
              ·
                refine ⟨12450838744624264554797005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16601118326165686073062673 12450838744624264554797005)
                ·
                  refine ⟨4669064529234099208048877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12450838744624264554797005 4669064529234099208048877)
                  ·
                    refine ⟨1750899198462787203018329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4669064529234099208048877 1750899198462787203018329)
                    ·
                      refine ⟨1313174398847090402263747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1750899198462787203018329 1313174398847090402263747)
                      ·
                        rfl

theorem cell23_2557398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_2557398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557398 prefixEnd_2557398 := by exact prefixLift 2557398
  have htrace : WordTrace (prefixWord ++ tailWord_2557398) baseStart_2557398 baseEnd_2557398 := by
    simpa [prefixWord, tailWord_2557398, baseEnd_2557398] using wordTrace_append hprefix tailTrace_2557398
  have hstable : (prefixWord ++ tailWord_2557398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557398).length < 2 ^ (prefixWord ++ tailWord_2557398).sum := by decide
  have hdescent : baseEnd_2557398 < baseStart_2557398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557411 : List Nat := [1, 1, 1, 6, 2, 1, 1, 3, 1, 4, 2]
def baseStart_2557411 : Nat := 118140960795 + 2557411 * 2 ^ 59
def prefixEnd_2557411 : Nat := 4983230072969 + 3 ^ 40 * 2557411 * 2
def baseEnd_2557411 : Nat := 1313181074095598851401187

theorem tailTrace_2557411 : CollatzResearch.WordTrace tailWord_2557411 prefixEnd_2557411 1313181074095598851401187 := by
  unfold tailWord_2557411
  simp only [CollatzResearch.WordTrace]
  refine ⟨93276442137944192870792087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62184294758629461913861391 93276442137944192870792087)
  ·
    refine ⟨139914663206916289306188131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93276442137944192870792087 139914663206916289306188131)
    ·
      refine ⟨209871994810374433959282197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139914663206916289306188131 209871994810374433959282197)
      ·
        refine ⟨9837749756736301591841353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 209871994810374433959282197 9837749756736301591841353)
        ·
          refine ⟨7378312317552226193881015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9837749756736301591841353 7378312317552226193881015)
          ·
            refine ⟨11067468476328339290821523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7378312317552226193881015 11067468476328339290821523)
            ·
              refine ⟨16601202714492508936232285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11067468476328339290821523 16601202714492508936232285)
              ·
                refine ⟨6225451017934690851087107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16601202714492508936232285 6225451017934690851087107)
                ·
                  refine ⟨9338176526902036276630661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6225451017934690851087107 9338176526902036276630661)
                  ·
                    refine ⟨1750908098794131801868249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9338176526902036276630661 1750908098794131801868249)
                    ·
                      refine ⟨1313181074095598851401187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1750908098794131801868249 1313181074095598851401187)
                      ·
                        rfl

theorem cell23_2557411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_2557411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557411 prefixEnd_2557411 := by exact prefixLift 2557411
  have htrace : WordTrace (prefixWord ++ tailWord_2557411) baseStart_2557411 baseEnd_2557411 := by
    simpa [prefixWord, tailWord_2557411, baseEnd_2557411] using wordTrace_append hprefix tailTrace_2557411
  have hstable : (prefixWord ++ tailWord_2557411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557411).length < 2 ^ (prefixWord ++ tailWord_2557411).sum := by decide
  have hdescent : baseEnd_2557411 < baseStart_2557411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557457 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 7]
def baseStart_2557457 : Nat := 118140960795 + 2557457 * 2 ^ 59
def prefixEnd_2557457 : Nat := 4983230072969 + 3 ^ 40 * 2557457 * 2
def baseEnd_2557457 : Nat := 1313204694205705671425975

theorem tailTrace_2557457 : CollatzResearch.WordTrace tailWord_2557457 prefixEnd_2557457 1313204694205705671425975 := by
  unfold tailWord_2557457
  simp only [CollatzResearch.WordTrace]
  refine ⟨93278119895777542726966625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62185413263851695151311083 93278119895777542726966625)
  ·
    refine ⟨69958589921833157045224969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93278119895777542726966625 69958589921833157045224969)
    ·
      refine ⟨52468942441374867783918727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69958589921833157045224969 52468942441374867783918727)
      ·
        refine ⟨78703413662062301675878091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52468942441374867783918727 78703413662062301675878091)
        ·
          refine ⟨118055120493093452513817137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78703413662062301675878091 118055120493093452513817137)
          ·
            refine ⟨88541340369820089385362853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118055120493093452513817137 88541340369820089385362853)
            ·
              refine ⟨16601501319341266759755535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88541340369820089385362853 16601501319341266759755535)
              ·
                refine ⟨24902251979011900139633303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16601501319341266759755535 24902251979011900139633303)
                ·
                  refine ⟨37353377968517850209449955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24902251979011900139633303 37353377968517850209449955)
                  ·
                    refine ⟨56030066952776775314174933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37353377968517850209449955 56030066952776775314174933)
                    ·
                      refine ⟨1313204694205705671425975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56030066952776775314174933 1313204694205705671425975)
                      ·
                        rfl

theorem cell23_2557457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_2557457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557457 prefixEnd_2557457 := by exact prefixLift 2557457
  have htrace : WordTrace (prefixWord ++ tailWord_2557457) baseStart_2557457 baseEnd_2557457 := by
    simpa [prefixWord, tailWord_2557457, baseEnd_2557457] using wordTrace_append hprefix tailTrace_2557457
  have hstable : (prefixWord ++ tailWord_2557457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557457).length < 2 ^ (prefixWord ++ tailWord_2557457).sum := by decide
  have hdescent : baseEnd_2557457 < baseStart_2557457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557477 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 1, 10]
def baseStart_2557477 : Nat := 118140960795 + 2557477 * 2 ^ 59
def prefixEnd_2557477 : Nat := 4983230072969 + 3 ^ 40 * 2557477 * 2
def baseEnd_2557477 : Nat := 437738321272931864391961

theorem tailTrace_2557477 : CollatzResearch.WordTrace tailWord_2557477 prefixEnd_2557477 437738321272931864391961 := by
  unfold tailWord_2557477
  simp only [CollatzResearch.WordTrace]
  refine ⟨93278849355705086142694685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62185899570470057428463123 93278849355705086142694685)
  ·
    refine ⟨34979568508389407303510507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93278849355705086142694685 34979568508389407303510507)
    ·
      refine ⟨52469352762584110955265761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34979568508389407303510507 52469352762584110955265761)
      ·
        refine ⟨39352014571938083216449321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52469352762584110955265761 39352014571938083216449321)
        ·
          refine ⟨29514010928953562412336991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39352014571938083216449321 29514010928953562412336991)
          ·
            refine ⟨44271016393430343618505487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29514010928953562412336991 44271016393430343618505487)
            ·
              refine ⟨66406524590145515427758231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44271016393430343618505487 66406524590145515427758231)
              ·
                refine ⟨99609786885218273141637347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66406524590145515427758231 99609786885218273141637347)
                ·
                  refine ⟨149414680327827409712456021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99609786885218273141637347 149414680327827409712456021)
                  ·
                    refine ⟨437738321272931864391961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 149414680327827409712456021 437738321272931864391961)
                    ·
                      rfl

theorem cell23_2557477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_2557477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557477 prefixEnd_2557477 := by exact prefixLift 2557477
  have htrace : WordTrace (prefixWord ++ tailWord_2557477) baseStart_2557477 baseEnd_2557477 := by
    simpa [prefixWord, tailWord_2557477, baseEnd_2557477] using wordTrace_append hprefix tailTrace_2557477
  have hstable : (prefixWord ++ tailWord_2557477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557477).length < 2 ^ (prefixWord ++ tailWord_2557477).sum := by decide
  have hdescent : baseEnd_2557477 < baseStart_2557477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557558 : List Nat := [5, 1, 1, 2, 2, 2, 2, 2, 6]
def baseStart_2557558 : Nat := 118140960795 + 2557558 * 2 ^ 59
def prefixEnd_2557558 : Nat := 4983230072969 + 3 ^ 40 * 2557558 * 2
def baseEnd_2557558 : Nat := 145917395083534419584779

theorem tailTrace_2557558 : CollatzResearch.WordTrace tailWord_2557558 prefixEnd_2557558 145917395083534419584779 := by
  unfold tailWord_2557558
  simp only [CollatzResearch.WordTrace]
  refine ⟨5830112729275727311024583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62187869112274424650928885 5830112729275727311024583)
  ·
    refine ⟨8745169093913590966536875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5830112729275727311024583 8745169093913590966536875)
    ·
      refine ⟨13117753640870386449805313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8745169093913590966536875 13117753640870386449805313)
      ·
        refine ⟨9838315230652789837353985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13117753640870386449805313 9838315230652789837353985)
        ·
          refine ⟨7378736422989592378015489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9838315230652789837353985 7378736422989592378015489)
          ·
            refine ⟨5534052317242194283511617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7378736422989592378015489 5534052317242194283511617)
            ·
              refine ⟨4150539237931645712633713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5534052317242194283511617 4150539237931645712633713)
              ·
                refine ⟨3112904428448734284475285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4150539237931645712633713 3112904428448734284475285)
                ·
                  refine ⟨145917395083534419584779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3112904428448734284475285 145917395083534419584779)
                  ·
                    rfl

theorem cell23_2557558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_2557558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557558 prefixEnd_2557558 := by exact prefixLift 2557558
  have htrace : WordTrace (prefixWord ++ tailWord_2557558) baseStart_2557558 baseEnd_2557558 := by
    simpa [prefixWord, tailWord_2557558, baseEnd_2557558] using wordTrace_append hprefix tailTrace_2557558
  have hstable : (prefixWord ++ tailWord_2557558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557558).length < 2 ^ (prefixWord ++ tailWord_2557558).sum := by decide
  have hdescent : baseEnd_2557558 < baseStart_2557558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557591 : List Nat := [1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 4]
def baseStart_2557591 : Nat := 118140960795 + 2557591 * 2 ^ 59
def prefixEnd_2557591 : Nat := 4983230072969 + 3 ^ 40 * 2557591 * 2
def baseEnd_2557591 : Nat := 1313273500613408147150359

theorem tailTrace_2557591 : CollatzResearch.WordTrace tailWord_2557591 prefixEnd_2557591 1313273500613408147150359 := by
  unfold tailWord_2557591
  simp only [CollatzResearch.WordTrace]
  refine ⟨93283007277292083612344627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62188671518194722408229751 93283007277292083612344627)
  ·
    refine ⟨139924510915938125418516941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93283007277292083612344627 139924510915938125418516941)
    ·
      refine ⟨52471691593476797031943853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139924510915938125418516941 52471691593476797031943853)
      ·
        refine ⟨19676884347553798886978945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52471691593476797031943853 19676884347553798886978945)
        ·
          refine ⟨14757663260665349165234209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19676884347553798886978945 14757663260665349165234209)
          ·
            refine ⟨11068247445499011873925657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14757663260665349165234209 11068247445499011873925657)
            ·
              refine ⟨8301185584124258905444243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11068247445499011873925657 8301185584124258905444243)
              ·
                refine ⟨12451778376186388358166365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8301185584124258905444243 12451778376186388358166365)
                ·
                  refine ⟨4669416891069895634312387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12451778376186388358166365 4669416891069895634312387)
                  ·
                    refine ⟨7004125336604843451468581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4669416891069895634312387 7004125336604843451468581)
                    ·
                      refine ⟨1313273500613408147150359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7004125336604843451468581 1313273500613408147150359)
                      ·
                        rfl

theorem cell23_2557591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_2557591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557591 prefixEnd_2557591 := by exact prefixLift 2557591
  have htrace : WordTrace (prefixWord ++ tailWord_2557591) baseStart_2557591 baseEnd_2557591 := by
    simpa [prefixWord, tailWord_2557591, baseEnd_2557591] using wordTrace_append hprefix tailTrace_2557591
  have hstable : (prefixWord ++ tailWord_2557591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557591).length < 2 ^ (prefixWord ++ tailWord_2557591).sum := by decide
  have hdescent : baseEnd_2557591 < baseStart_2557591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557601 : List Nat := [1, 2, 3, 3, 2, 1, 2, 2, 1, 6]
def baseStart_2557601 : Nat := 118140960795 + 2557601 * 2 ^ 59
def prefixEnd_2557601 : Nat := 4983230072969 + 3 ^ 40 * 2557601 * 2
def baseEnd_2557601 : Nat := 437759545139984369341771

theorem tailTrace_2557601 : CollatzResearch.WordTrace tailWord_2557601 prefixEnd_2557601 437759545139984369341771 := by
  unfold tailWord_2557601
  simp only [CollatzResearch.WordTrace]
  refine ⟨93283372007255855320208657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62188914671503903546805771 93283372007255855320208657)
  ·
    refine ⟨69962529005441891490156493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93283372007255855320208657 69962529005441891490156493)
    ·
      refine ⟨26235948377040709308808685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69962529005441891490156493 26235948377040709308808685)
      ·
        refine ⟨9838480641390265990803257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26235948377040709308808685 9838480641390265990803257)
        ·
          refine ⟨7378860481042699493102443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9838480641390265990803257 7378860481042699493102443)
          ·
            refine ⟨11068290721564049239653665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7378860481042699493102443 11068290721564049239653665)
            ·
              refine ⟨8301218041173036929740249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11068290721564049239653665 8301218041173036929740249)
              ·
                refine ⟨6225913530879777697305187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8301218041173036929740249 6225913530879777697305187)
                ·
                  refine ⟨9338870296319666545957781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6225913530879777697305187 9338870296319666545957781)
                  ·
                    refine ⟨437759545139984369341771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9338870296319666545957781 437759545139984369341771)
                    ·
                      rfl

theorem cell23_2557601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_2557601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557601 prefixEnd_2557601 := by exact prefixLift 2557601
  have htrace : WordTrace (prefixWord ++ tailWord_2557601) baseStart_2557601 baseEnd_2557601 := by
    simpa [prefixWord, tailWord_2557601, baseEnd_2557601] using wordTrace_append hprefix tailTrace_2557601
  have hstable : (prefixWord ++ tailWord_2557601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557601).length < 2 ^ (prefixWord ++ tailWord_2557601).sum := by decide
  have hdescent : baseEnd_2557601 < baseStart_2557601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557618 : List Nat := [3, 2, 1, 1, 1, 2, 5, 2, 2, 4]
def baseStart_2557618 : Nat := 118140960795 + 2557618 * 2 ^ 59
def prefixEnd_2557618 : Nat := 4983230072969 + 3 ^ 40 * 2557618 * 2
def baseEnd_2557618 : Nat := 437762454863693180504245

theorem tailTrace_2557618 : CollatzResearch.WordTrace tailWord_2557618 prefixEnd_2557618 437762454863693180504245 := by
  unfold tailWord_2557618
  simp only [CollatzResearch.WordTrace]
  refine ⟨23320998012048566805894377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62189328032129511482385005 23320998012048566805894377)
  ·
    refine ⟨17490748509036425104420783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23320998012048566805894377 17490748509036425104420783)
    ·
      refine ⟨26236122763554637656631175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17490748509036425104420783 26236122763554637656631175)
      ·
        refine ⟨39354184145331956484946763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26236122763554637656631175 39354184145331956484946763)
        ·
          refine ⟨59031276217997934727420145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39354184145331956484946763 59031276217997934727420145)
          ·
            refine ⟨44273457163498451045565109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59031276217997934727420145 44273457163498451045565109)
            ·
              refine ⟨4150636609077979785521729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44273457163498451045565109 4150636609077979785521729)
              ·
                refine ⟨3112977456808484839141297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4150636609077979785521729 3112977456808484839141297)
                ·
                  refine ⟨2334733092606363629355973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3112977456808484839141297 2334733092606363629355973)
                  ·
                    refine ⟨437762454863693180504245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2334733092606363629355973 437762454863693180504245)
                    ·
                      rfl

theorem cell23_2557618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_2557618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557618 prefixEnd_2557618 := by exact prefixLift 2557618
  have htrace : WordTrace (prefixWord ++ tailWord_2557618) baseStart_2557618 baseEnd_2557618 := by
    simpa [prefixWord, tailWord_2557618, baseEnd_2557618] using wordTrace_append hprefix tailTrace_2557618
  have hstable : (prefixWord ++ tailWord_2557618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557618).length < 2 ^ (prefixWord ++ tailWord_2557618).sum := by decide
  have hdescent : baseEnd_2557618 < baseStart_2557618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557658 : List Nat := [3, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3]
def baseStart_2557658 : Nat := 118140960795 + 2557658 * 2 ^ 59
def prefixEnd_2557658 : Nat := 4983230072969 + 3 ^ 40 * 2557658 * 2
def baseEnd_2557658 : Nat := 1313307903817259385012551

theorem tailTrace_2557658 : CollatzResearch.WordTrace tailWord_2557658 prefixEnd_2557658 1313307903817259385012551 := by
  unfold tailWord_2557658
  simp only [CollatzResearch.WordTrace]
  refine ⟨23321362742012338513758407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62190300645366236036689085 23321362742012338513758407)
  ·
    refine ⟨34982044113018507770637611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23321362742012338513758407 34982044113018507770637611)
    ·
      refine ⟨52473066169527761655956417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34982044113018507770637611 52473066169527761655956417)
      ·
        refine ⟨39354799627145821241967313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52473066169527761655956417 39354799627145821241967313)
        ·
          refine ⟨29516099720359365931475485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39354799627145821241967313 29516099720359365931475485)
          ·
            refine ⟨11068537395134762224303307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29516099720359365931475485 11068537395134762224303307)
            ·
              refine ⟨16602806092702143336454961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11068537395134762224303307 16602806092702143336454961)
              ·
                refine ⟨12452104569526607502341221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16602806092702143336454961 12452104569526607502341221)
                ·
                  refine ⟨2334769606786238906688979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12452104569526607502341221 2334769606786238906688979)
                  ·
                    refine ⟨3502154410179358360033469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2334769606786238906688979 3502154410179358360033469)
                    ·
                      refine ⟨1313307903817259385012551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3502154410179358360033469 1313307903817259385012551)
                      ·
                        rfl

theorem cell23_2557658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_2557658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557658 prefixEnd_2557658 := by exact prefixLift 2557658
  have htrace : WordTrace (prefixWord ++ tailWord_2557658) baseStart_2557658 baseEnd_2557658 := by
    simpa [prefixWord, tailWord_2557658, baseEnd_2557658] using wordTrace_append hprefix tailTrace_2557658
  have hstable : (prefixWord ++ tailWord_2557658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557658).length < 2 ^ (prefixWord ++ tailWord_2557658).sum := by decide
  have hdescent : baseEnd_2557658 < baseStart_2557658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557726 : List Nat := [4, 3, 2, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_2557726 : Nat := 118140960795 + 2557726 * 2 ^ 59
def prefixEnd_2557726 : Nat := 4983230072969 + 3 ^ 40 * 2557726 * 2
def baseEnd_2557726 : Nat := 1313342820501765118962239

theorem tailTrace_2557726 : CollatzResearch.WordTrace tailWord_2557726 prefixEnd_2557726 1313342820501765118962239 := by
  unfold tailWord_2557726
  simp only [CollatzResearch.WordTrace]
  refine ⟨11660991391475375208563629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62191954087868667779006021 11660991391475375208563629)
  ·
    refine ⟨4372871771803265703211361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11660991391475375208563629 4372871771803265703211361)
    ·
      refine ⟨3279653828852449277408521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4372871771803265703211361 3279653828852449277408521)
      ·
        refine ⟨2459740371639336958056391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3279653828852449277408521 2459740371639336958056391)
        ·
          refine ⟨3689610557459005437084587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2459740371639336958056391 3689610557459005437084587)
          ·
            refine ⟨5534415836188508155626881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3689610557459005437084587 5534415836188508155626881)
            ·
              refine ⟨4150811877141381116720161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5534415836188508155626881 4150811877141381116720161)
              ·
                refine ⟨3113108907856035837540121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4150811877141381116720161 3113108907856035837540121)
                ·
                  refine ⟨2334831680892026878155091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3113108907856035837540121 2334831680892026878155091)
                  ·
                    refine ⟨3502247521338040317232637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2334831680892026878155091 3502247521338040317232637)
                    ·
                      refine ⟨1313342820501765118962239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3502247521338040317232637 1313342820501765118962239)
                      ·
                        rfl

theorem cell23_2557726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_2557726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557726 prefixEnd_2557726 := by exact prefixLift 2557726
  have htrace : WordTrace (prefixWord ++ tailWord_2557726) baseStart_2557726 baseEnd_2557726 := by
    simpa [prefixWord, tailWord_2557726, baseEnd_2557726] using wordTrace_append hprefix tailTrace_2557726
  have hstable : (prefixWord ++ tailWord_2557726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557726).length < 2 ^ (prefixWord ++ tailWord_2557726).sum := by decide
  have hdescent : baseEnd_2557726 < baseStart_2557726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557732 : List Nat := [2, 3, 1, 3, 2, 1, 1, 4, 2, 2, 2]
def baseStart_2557732 : Nat := 118140960795 + 2557732 * 2 ^ 59
def prefixEnd_2557732 : Nat := 4983230072969 + 3 ^ 40 * 2557732 * 2
def baseEnd_2557732 : Nat := 1313345901385692095487211

theorem tailTrace_2557732 : CollatzResearch.WordTrace tailWord_2557732 prefixEnd_2557732 1313345901385692095487211 := by
  unfold tailWord_2557732
  simp only [CollatzResearch.WordTrace]
  refine ⟨46644074984890632346613725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62192099979854176462151633 46644074984890632346613725)
  ·
    refine ⟨17491528119333987129980147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46644074984890632346613725 17491528119333987129980147)
    ·
      refine ⟨26237292179000980694970221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17491528119333987129980147 26237292179000980694970221)
      ·
        refine ⟨9838984567125367760613833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26237292179000980694970221 9838984567125367760613833)
        ·
          refine ⟨7379238425344025820460375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9838984567125367760613833 7379238425344025820460375)
          ·
            refine ⟨11068857638016038730690563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7379238425344025820460375 11068857638016038730690563)
            ·
              refine ⟨16603286457024058096035845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11068857638016038730690563 16603286457024058096035845)
              ·
                refine ⟨3113116210692010893006721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16603286457024058096035845 3113116210692010893006721)
                ·
                  refine ⟨2334837158019008169755041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3113116210692010893006721 2334837158019008169755041)
                  ·
                    refine ⟨1751127868514256127316281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2334837158019008169755041 1751127868514256127316281)
                    ·
                      refine ⟨1313345901385692095487211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1751127868514256127316281 1313345901385692095487211)
                      ·
                        rfl

theorem cell23_2557732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_2557732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557732 prefixEnd_2557732 := by exact prefixLift 2557732
  have htrace : WordTrace (prefixWord ++ tailWord_2557732) baseStart_2557732 baseEnd_2557732 := by
    simpa [prefixWord, tailWord_2557732, baseEnd_2557732] using wordTrace_append hprefix tailTrace_2557732
  have hstable : (prefixWord ++ tailWord_2557732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557732).length < 2 ^ (prefixWord ++ tailWord_2557732).sum := by decide
  have hdescent : baseEnd_2557732 < baseStart_2557732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557768 : List Nat := [2, 1, 3, 1, 1, 4, 3, 1, 2, 5]
def baseStart_2557768 : Nat := 118140960795 + 2557768 * 2 ^ 59
def prefixEnd_2557768 : Nat := 4983230072969 + 3 ^ 40 * 2557768 * 2
def baseEnd_2557768 : Nat := 437788128896417984879015

theorem tailTrace_2557768 : CollatzResearch.WordTrace tailWord_2557768 prefixEnd_2557768 437788128896417984879015 := by
  unfold tailWord_2557768
  simp only [CollatzResearch.WordTrace]
  refine ⟨46644731498825421420768979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62192975331767228561025305 46644731498825421420768979)
  ·
    refine ⟨69967097248238132131153469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46644731498825421420768979 69967097248238132131153469)
    ·
      refine ⟨26237661468089299549182551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69967097248238132131153469 26237661468089299549182551)
      ·
        refine ⟨39356492202133949323773827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26237661468089299549182551 39356492202133949323773827)
        ·
          refine ⟨59034738303200923985660741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39356492202133949323773827 59034738303200923985660741)
          ·
            refine ⟨11069013431850173247311389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59034738303200923985660741 11069013431850173247311389)
            ·
              refine ⟨4150880036943814967741771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11069013431850173247311389 4150880036943814967741771)
              ·
                refine ⟨6226320055415722451612657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4150880036943814967741771 6226320055415722451612657)
                ·
                  refine ⟨4669740041561791838709493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6226320055415722451612657 4669740041561791838709493)
                  ·
                    refine ⟨437788128896417984879015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4669740041561791838709493 437788128896417984879015)
                    ·
                      rfl

theorem cell23_2557768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_2557768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557768 prefixEnd_2557768 := by exact prefixLift 2557768
  have htrace : WordTrace (prefixWord ++ tailWord_2557768) baseStart_2557768 baseEnd_2557768 := by
    simpa [prefixWord, tailWord_2557768, baseEnd_2557768] using wordTrace_append hprefix tailTrace_2557768
  have hstable : (prefixWord ++ tailWord_2557768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557768).length < 2 ^ (prefixWord ++ tailWord_2557768).sum := by decide
  have hdescent : baseEnd_2557768 < baseStart_2557768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557805 : List Nat := [1, 5, 1, 1, 1, 1, 4, 1, 2, 4, 2]
def baseStart_2557805 : Nat := 118140960795 + 2557805 * 2 ^ 59
def prefixEnd_2557805 : Nat := 4983230072969 + 3 ^ 40 * 2557805 * 2
def baseEnd_2557805 : Nat := 1313383385473470309874375

theorem tailTrace_2557805 : CollatzResearch.WordTrace tailWord_2557805 prefixEnd_2557805 1313383385473470309874375 := by
  unfold tailWord_2557805
  simp only [CollatzResearch.WordTrace]
  refine ⟨93290812498516798160634869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62193874999011198773756579 93290812498516798160634869)
  ·
    refine ⟨8746013671735949827559519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93290812498516798160634869 8746013671735949827559519)
    ·
      refine ⟨13119020507603924741339279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8746013671735949827559519 13119020507603924741339279)
      ·
        refine ⟨19678530761405887112008919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13119020507603924741339279 19678530761405887112008919)
        ·
          refine ⟨29517796142108830668013379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19678530761405887112008919 29517796142108830668013379)
          ·
            refine ⟨44276694213163246002020069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29517796142108830668013379 44276694213163246002020069)
            ·
              refine ⟨8301880164968108625378763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44276694213163246002020069 8301880164968108625378763)
              ·
                refine ⟨12452820247452162938068145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8301880164968108625378763 12452820247452162938068145)
                ·
                  refine ⟨9339615185589122203551109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12452820247452162938068145 9339615185589122203551109)
                  ·
                    refine ⟨1751177847297960413165833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9339615185589122203551109 1751177847297960413165833)
                    ·
                      refine ⟨1313383385473470309874375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1751177847297960413165833 1313383385473470309874375)
                      ·
                        rfl

theorem cell23_2557805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_2557805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557805 prefixEnd_2557805 := by exact prefixLift 2557805
  have htrace : WordTrace (prefixWord ++ tailWord_2557805) baseStart_2557805 baseEnd_2557805 := by
    simpa [prefixWord, tailWord_2557805, baseEnd_2557805] using wordTrace_append hprefix tailTrace_2557805
  have hstable : (prefixWord ++ tailWord_2557805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557805).length < 2 ^ (prefixWord ++ tailWord_2557805).sum := by decide
  have hdescent : baseEnd_2557805 < baseStart_2557805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557842 : List Nat := [3, 2, 3, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_2557842 : Nat := 118140960795 + 2557842 * 2 ^ 59
def prefixEnd_2557842 : Nat := 4983230072969 + 3 ^ 40 * 2557842 * 2
def baseEnd_2557842 : Nat := 1313402384257686665111705

theorem tailTrace_2557842 : CollatzResearch.WordTrace tailWord_2557842 prefixEnd_2557842 1313402384257686665111705 := by
  unfold tailWord_2557842
  simp only [CollatzResearch.WordTrace]
  refine ⟨23323040499845688369932945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62194774666255168986487853 23323040499845688369932945)
  ·
    refine ⟨17492280374884266277449709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23323040499845688369932945 17492280374884266277449709)
    ·
      refine ⟨6559605140581599854043641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17492280374884266277449709 6559605140581599854043641)
      ·
        refine ⟨4919703855436199890532731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6559605140581599854043641 4919703855436199890532731)
        ·
          refine ⟨7379555783154299835799097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4919703855436199890532731 7379555783154299835799097)
          ·
            refine ⟨5534666837365724876849323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7379555783154299835799097 5534666837365724876849323)
            ·
              refine ⟨8302000256048587315273985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5534666837365724876849323 8302000256048587315273985)
              ·
                refine ⟨6226500192036440486455489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8302000256048587315273985 6226500192036440486455489)
                ·
                  refine ⟨4669875144027330364841617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6226500192036440486455489 4669875144027330364841617)
                  ·
                    refine ⟨3502406358020497773631213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4669875144027330364841617 3502406358020497773631213)
                    ·
                      refine ⟨1313402384257686665111705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3502406358020497773631213 1313402384257686665111705)
                      ·
                        rfl

theorem cell23_2557842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_2557842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557842 prefixEnd_2557842 := by exact prefixLift 2557842
  have htrace : WordTrace (prefixWord ++ tailWord_2557842) baseStart_2557842 baseEnd_2557842 := by
    simpa [prefixWord, tailWord_2557842, baseEnd_2557842] using wordTrace_append hprefix tailTrace_2557842
  have hstable : (prefixWord ++ tailWord_2557842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557842).length < 2 ^ (prefixWord ++ tailWord_2557842).sum := by decide
  have hdescent : baseEnd_2557842 < baseStart_2557842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557888 : List Nat := [2, 1, 1, 2, 3, 2, 3, 2, 1, 6]
def baseStart_2557888 : Nat := 118140960795 + 2557888 * 2 ^ 59
def prefixEnd_2557888 : Nat := 4983230072969 + 3 ^ 40 * 2557888 * 2
def baseEnd_2557888 : Nat := 437808668122597828378831

theorem tailTrace_2557888 : CollatzResearch.WordTrace tailWord_2557888 prefixEnd_2557888 437808668122597828378831 := by
  unfold tailWord_2557888
  simp only [CollatzResearch.WordTrace]
  refine ⟨46646919878608051667953159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62195893171477402223937545 46646919878608051667953159)
  ·
    refine ⟨69970379817912077501929739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46646919878608051667953159 69970379817912077501929739)
    ·
      refine ⟨104955569726868116252894609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69970379817912077501929739 104955569726868116252894609)
      ·
        refine ⟨78716677295151087189670957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104955569726868116252894609 78716677295151087189670957)
        ·
          refine ⟨29518753985681657696126609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78716677295151087189670957 29518753985681657696126609)
          ·
            refine ⟨22139065489261243272094957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29518753985681657696126609 22139065489261243272094957)
            ·
              refine ⟨8302149558472966227035609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22139065489261243272094957 8302149558472966227035609)
              ·
                refine ⟨6226612168854724670276707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8302149558472966227035609 6226612168854724670276707)
                ·
                  refine ⟨9339918253282087005415061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6226612168854724670276707 9339918253282087005415061)
                  ·
                    refine ⟨437808668122597828378831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9339918253282087005415061 437808668122597828378831)
                    ·
                      rfl

theorem cell23_2557888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 1, 6].length) (baseStart_2557888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557888 prefixEnd_2557888 := by exact prefixLift 2557888
  have htrace : WordTrace (prefixWord ++ tailWord_2557888) baseStart_2557888 baseEnd_2557888 := by
    simpa [prefixWord, tailWord_2557888, baseEnd_2557888] using wordTrace_append hprefix tailTrace_2557888
  have hstable : (prefixWord ++ tailWord_2557888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557888).length < 2 ^ (prefixWord ++ tailWord_2557888).sum := by decide
  have hdescent : baseEnd_2557888 < baseStart_2557888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557906 : List Nat := [3, 2, 2, 3, 2, 1, 1, 4, 1, 1, 3]
def baseStart_2557906 : Nat := 118140960795 + 2557906 * 2 ^ 59
def prefixEnd_2557906 : Nat := 4983230072969 + 3 ^ 40 * 2557906 * 2
def baseEnd_2557906 : Nat := 1313435247019574414711411

theorem tailTrace_2557906 : CollatzResearch.WordTrace tailWord_2557906 prefixEnd_2557906 1313435247019574414711411 := by
  unfold tailWord_2557906
  simp only [CollatzResearch.WordTrace]
  refine ⟨23323624067787723102515393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62196330847433928273374381 23323624067787723102515393)
  ·
    refine ⟨17492718050840792326886545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23323624067787723102515393 17492718050840792326886545)
    ·
      refine ⟨13119538538130594245164909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17492718050840792326886545 13119538538130594245164909)
      ·
        refine ⟨4919826951798972841936841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13119538538130594245164909 4919826951798972841936841)
        ·
          refine ⟨3689870213849229631452631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4919826951798972841936841 3689870213849229631452631)
          ·
            refine ⟨5534805320773844447178947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3689870213849229631452631 5534805320773844447178947)
            ·
              refine ⟨8302207981160766670768421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5534805320773844447178947 8302207981160766670768421)
              ·
                refine ⟨1556663996467643750769079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8302207981160766670768421 1556663996467643750769079)
                ·
                  refine ⟨2334995994701465626153619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1556663996467643750769079 2334995994701465626153619)
                  ·
                    refine ⟨3502493992052198439230429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2334995994701465626153619 3502493992052198439230429)
                    ·
                      refine ⟨1313435247019574414711411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3502493992052198439230429 1313435247019574414711411)
                      ·
                        rfl

theorem cell23_2557906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_2557906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557906 prefixEnd_2557906 := by exact prefixLift 2557906
  have htrace : WordTrace (prefixWord ++ tailWord_2557906) baseStart_2557906 baseEnd_2557906 := by
    simpa [prefixWord, tailWord_2557906, baseEnd_2557906] using wordTrace_append hprefix tailTrace_2557906
  have hstable : (prefixWord ++ tailWord_2557906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557906).length < 2 ^ (prefixWord ++ tailWord_2557906).sum := by decide
  have hdescent : baseEnd_2557906 < baseStart_2557906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557912 : List Nat := [2, 1, 2, 2, 2, 2, 2, 3, 3, 2, 2]
def baseStart_2557912 : Nat := 118140960795 + 2557912 * 2 ^ 59
def prefixEnd_2557912 : Nat := 4983230072969 + 3 ^ 40 * 2557912 * 2
def baseEnd_2557912 : Nat := 1313438327903501391236383

theorem tailTrace_2557912 : CollatzResearch.WordTrace tailWord_2557912 prefixEnd_2557912 1313438327903501391236383 := by
  unfold tailWord_2557912
  simp only [CollatzResearch.WordTrace]
  refine ⟨46647357554564577717389995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62196476739419436956519993 46647357554564577717389995)
  ·
    refine ⟨69971036331846866576084993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46647357554564577717389995 69971036331846866576084993)
    ·
      refine ⟨52478277248885149932063745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69971036331846866576084993 52478277248885149932063745)
      ·
        refine ⟨39358707936663862449047809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52478277248885149932063745 39358707936663862449047809)
        ·
          refine ⟨29519030952497896836785857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39358707936663862449047809 29519030952497896836785857)
          ·
            refine ⟨22139273214373422627589393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29519030952497896836785857 22139273214373422627589393)
            ·
              refine ⟨16604454910780066970692045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22139273214373422627589393 16604454910780066970692045)
              ·
                refine ⟨6226670591542525114009517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16604454910780066970692045 6226670591542525114009517)
                ·
                  refine ⟨2335001471828446917753569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6226670591542525114009517 2335001471828446917753569)
                  ·
                    refine ⟨1751251103871335188315177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2335001471828446917753569 1751251103871335188315177)
                    ·
                      refine ⟨1313438327903501391236383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1751251103871335188315177 1313438327903501391236383)
                      ·
                        rfl

theorem cell23_2557912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 3, 2, 2].length) (baseStart_2557912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557912 prefixEnd_2557912 := by exact prefixLift 2557912
  have htrace : WordTrace (prefixWord ++ tailWord_2557912) baseStart_2557912 baseEnd_2557912 := by
    simpa [prefixWord, tailWord_2557912, baseEnd_2557912] using wordTrace_append hprefix tailTrace_2557912
  have hstable : (prefixWord ++ tailWord_2557912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557912).length < 2 ^ (prefixWord ++ tailWord_2557912).sum := by decide
  have hdescent : baseEnd_2557912 < baseStart_2557912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557933 : List Nat := [1, 5, 1, 4, 2, 1, 1, 1, 2, 3, 2]
def baseStart_2557933 : Nat := 118140960795 + 2557933 * 2 ^ 59
def prefixEnd_2557933 : Nat := 4983230072969 + 3 ^ 40 * 2557933 * 2
def baseEnd_2557933 : Nat := 1313449110997245809073787

theorem tailTrace_2557933 : CollatzResearch.WordTrace tailWord_2557933 prefixEnd_2557933 1313449110997245809073787 := by
  unfold tailWord_2557933
  simp only [CollatzResearch.WordTrace]
  refine ⟨93295481042053076021294453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62196987361368717347529635 93295481042053076021294453)
  ·
    refine ⟨8746451347692475876996355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93295481042053076021294453 8746451347692475876996355)
    ·
      refine ⟨13119677021538713815494533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8746451347692475876996355 13119677021538713815494533)
      ·
        refine ⟨2459939441538508840405225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13119677021538713815494533 2459939441538508840405225)
        ·
          refine ⟨1844954581153881630303919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2459939441538508840405225 1844954581153881630303919)
          ·
            refine ⟨2767431871730822445455879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1844954581153881630303919 2767431871730822445455879)
            ·
              refine ⟨4151147807596233668183819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2767431871730822445455879 4151147807596233668183819)
              ·
                refine ⟨6226721711394350502275729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4151147807596233668183819 6226721711394350502275729)
                ·
                  refine ⟨4670041283545762876706797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6226721711394350502275729 4670041283545762876706797)
                  ·
                    refine ⟨1751265481329661078765049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4670041283545762876706797 1751265481329661078765049)
                    ·
                      refine ⟨1313449110997245809073787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1751265481329661078765049 1313449110997245809073787)
                      ·
                        rfl

theorem cell23_2557933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_2557933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557933 prefixEnd_2557933 := by exact prefixLift 2557933
  have htrace : WordTrace (prefixWord ++ tailWord_2557933) baseStart_2557933 baseEnd_2557933 := by
    simpa [prefixWord, tailWord_2557933, baseEnd_2557933] using wordTrace_append hprefix tailTrace_2557933
  have hstable : (prefixWord ++ tailWord_2557933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557933).length < 2 ^ (prefixWord ++ tailWord_2557933).sum := by decide
  have hdescent : baseEnd_2557933 < baseStart_2557933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557945 : List Nat := [1, 2, 1, 3, 1, 4, 2, 2, 1, 3, 3]
def baseStart_2557945 : Nat := 118140960795 + 2557945 * 2 ^ 59
def prefixEnd_2557945 : Nat := 4983230072969 + 3 ^ 40 * 2557945 * 2
def baseEnd_2557945 : Nat := 1313455272765099762123731

theorem tailTrace_2557945 : CollatzResearch.WordTrace tailWord_2557945 prefixEnd_2557945 1313455272765099762123731 := by
  unfold tailWord_2557945
  simp only [CollatzResearch.WordTrace]
  refine ⟨93295918718009602070731289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62197279145339734713820859 93295918718009602070731289)
  ·
    refine ⟨69971939038507201553048467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93295918718009602070731289 69971939038507201553048467)
    ·
      refine ⟨104957908557760802329572701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69971939038507201553048467 104957908557760802329572701)
      ·
        refine ⟨39359215709160300873589763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104957908557760802329572701 39359215709160300873589763)
        ·
          refine ⟨59038823563740451310384645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39359215709160300873589763 59038823563740451310384645)
          ·
            refine ⟨11069779418201334620697121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59038823563740451310384645 11069779418201334620697121)
            ·
              refine ⟨8302334563651000965522841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11069779418201334620697121 8302334563651000965522841)
              ·
                refine ⟨6226750922738250724142131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8302334563651000965522841 6226750922738250724142131)
                ·
                  refine ⟨9340126384107376086213197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6226750922738250724142131 9340126384107376086213197)
                  ·
                    refine ⟨3502547394040266032329949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9340126384107376086213197 3502547394040266032329949)
                    ·
                      refine ⟨1313455272765099762123731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3502547394040266032329949 1313455272765099762123731)
                      ·
                        rfl

theorem cell23_2557945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_2557945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557945 prefixEnd_2557945 := by exact prefixLift 2557945
  have htrace : WordTrace (prefixWord ++ tailWord_2557945) baseStart_2557945 baseEnd_2557945 := by
    simpa [prefixWord, tailWord_2557945, baseEnd_2557945] using wordTrace_append hprefix tailTrace_2557945
  have hstable : (prefixWord ++ tailWord_2557945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557945).length < 2 ^ (prefixWord ++ tailWord_2557945).sum := by decide
  have hdescent : baseEnd_2557945 < baseStart_2557945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557956 : List Nat := [2, 3, 2, 4, 1, 2, 1, 2, 2, 4]
def baseStart_2557956 : Nat := 118140960795 + 2557956 * 2 ^ 59
def prefixEnd_2557956 : Nat := 4983230072969 + 3 ^ 40 * 2557956 * 2
def baseEnd_2557956 : Nat := 437820307017433073028727

theorem tailTrace_2557956 : CollatzResearch.WordTrace tailWord_2557956 prefixEnd_2557956 437820307017433073028727 := by
  unfold tailWord_2557956
  simp only [CollatzResearch.WordTrace]
  refine ⟨46648159960484875474690861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62197546613979833966254481 46648159960484875474690861)
  ·
    refine ⟨17493059985181828303009073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46648159960484875474690861 17493059985181828303009073)
    ·
      refine ⟨13119794988886371227256805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17493059985181828303009073 13119794988886371227256805)
      ·
        refine ⟨2459961560416194605110651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13119794988886371227256805 2459961560416194605110651)
        ·
          refine ⟨3689942340624291907665977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2459961560416194605110651 3689942340624291907665977)
          ·
            refine ⟨2767456755468218930749483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3689942340624291907665977 2767456755468218930749483)
            ·
              refine ⟨4151185133202328396124225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2767456755468218930749483 4151185133202328396124225)
              ·
                refine ⟨3113388849901746297093169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4151185133202328396124225 3113388849901746297093169)
                ·
                  refine ⟨2335041637426309722819877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3113388849901746297093169 2335041637426309722819877)
                  ·
                    refine ⟨437820307017433073028727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2335041637426309722819877 437820307017433073028727)
                    ·
                      rfl

theorem cell23_2557956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_2557956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557956 prefixEnd_2557956 := by exact prefixLift 2557956
  have htrace : WordTrace (prefixWord ++ tailWord_2557956) baseStart_2557956 baseEnd_2557956 := by
    simpa [prefixWord, tailWord_2557956, baseEnd_2557956] using wordTrace_append hprefix tailTrace_2557956
  have hstable : (prefixWord ++ tailWord_2557956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557956).length < 2 ^ (prefixWord ++ tailWord_2557956).sum := by decide
  have hdescent : baseEnd_2557956 < baseStart_2557956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2557989 : List Nat := [1, 3, 1, 2, 2, 4, 2, 2, 1, 3, 2]
def baseStart_2557989 : Nat := 118140960795 + 2557989 * 2 ^ 59
def prefixEnd_2557989 : Nat := 4983230072969 + 3 ^ 40 * 2557989 * 2
def baseEnd_2557989 : Nat := 1313477865913897589973529

theorem tailTrace_2557989 : CollatzResearch.WordTrace tailWord_2557989 prefixEnd_2557989 1313477865913897589973529 := by
  unfold tailWord_2557989
  simp only [CollatzResearch.WordTrace]
  refine ⟨93297523529850197585333021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62198349019900131723555347 93297523529850197585333021)
  ·
    refine ⟨34986571323693824094499883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93297523529850197585333021 34986571323693824094499883)
    ·
      refine ⟨52479856985540736141749825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34986571323693824094499883 52479856985540736141749825)
      ·
        refine ⟨39359892739155552106312369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52479856985540736141749825 39359892739155552106312369)
        ·
          refine ⟨29519919554366664079734277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39359892739155552106312369 29519919554366664079734277)
          ·
            refine ⟨5534984916443749514950177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29519919554366664079734277 5534984916443749514950177)
            ·
              refine ⟨4151238687332812136212633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5534984916443749514950177 4151238687332812136212633)
              ·
                refine ⟨3113429015499609102159475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4151238687332812136212633 3113429015499609102159475)
                ·
                  refine ⟨4670143523249413653239213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3113429015499609102159475 4670143523249413653239213)
                  ·
                    refine ⟨1751303821218530119964705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4670143523249413653239213 1751303821218530119964705)
                    ·
                      refine ⟨1313477865913897589973529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1751303821218530119964705 1313477865913897589973529)
                      ·
                        rfl

theorem cell23_2557989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 3, 2].length) (baseStart_2557989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2557989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2557989 prefixEnd_2557989 := by exact prefixLift 2557989
  have htrace : WordTrace (prefixWord ++ tailWord_2557989) baseStart_2557989 baseEnd_2557989 := by
    simpa [prefixWord, tailWord_2557989, baseEnd_2557989] using wordTrace_append hprefix tailTrace_2557989
  have hstable : (prefixWord ++ tailWord_2557989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2557989).length < 2 ^ (prefixWord ++ tailWord_2557989).sum := by decide
  have hdescent : baseEnd_2557989 < baseStart_2557989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2557989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558022 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_2558022 : Nat := 118140960795 + 2558022 * 2 ^ 59
def prefixEnd_2558022 : Nat := 4983230072969 + 3 ^ 40 * 2558022 * 2
def baseEnd_2558022 : Nat := 1313494810775495960860877

theorem tailTrace_2558022 : CollatzResearch.WordTrace tailWord_2558022 prefixEnd_2558022 1313494810775495960860877 := by
  unfold tailWord_2558022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2915585223085332631915135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 62199151425820429480856213 2915585223085332631915135)
  ·
    refine ⟨4373377834627998947872703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2915585223085332631915135 4373377834627998947872703)
    ·
      refine ⟨6560066751941998421809055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4373377834627998947872703 6560066751941998421809055)
      ·
        refine ⟨9840100127912997632713583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6560066751941998421809055 9840100127912997632713583)
        ·
          refine ⟨14760150191869496449070375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9840100127912997632713583 14760150191869496449070375)
          ·
            refine ⟨22140225287804244673605563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14760150191869496449070375 22140225287804244673605563)
            ·
              refine ⟨33210337931706367010408345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22140225287804244673605563 33210337931706367010408345)
              ·
                refine ⟨24907753448779775257806259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33210337931706367010408345 24907753448779775257806259)
                ·
                  refine ⟨37361630173169662886709389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24907753448779775257806259 37361630173169662886709389)
                  ·
                    refine ⟨14010611314938623582516021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37361630173169662886709389 14010611314938623582516021)
                    ·
                      refine ⟨1313494810775495960860877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14010611314938623582516021 1313494810775495960860877)
                      ·
                        rfl

theorem cell23_2558022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_2558022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558022 prefixEnd_2558022 := by exact prefixLift 2558022
  have htrace : WordTrace (prefixWord ++ tailWord_2558022) baseStart_2558022 baseEnd_2558022 := by
    simpa [prefixWord, tailWord_2558022, baseEnd_2558022] using wordTrace_append hprefix tailTrace_2558022
  have hstable : (prefixWord ++ tailWord_2558022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558022).length < 2 ^ (prefixWord ++ tailWord_2558022).sum := by decide
  have hdescent : baseEnd_2558022 < baseStart_2558022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558106 : List Nat := [3, 1, 1, 5, 3, 1, 1, 1, 2, 5]
def baseStart_2558106 : Nat := 118140960795 + 2558106 * 2 ^ 59
def prefixEnd_2558106 : Nat := 4983230072969 + 3 ^ 40 * 2558106 * 2
def baseEnd_2558106 : Nat := 437845981050157877403497

theorem tailTrace_2558106 : CollatzResearch.WordTrace tailWord_2558106 prefixEnd_2558106 437845981050157877403497 := by
  unfold tailWord_2558106
  simp only [CollatzResearch.WordTrace]
  refine ⟨23325447717606581641835543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62201193913617551044894781 23325447717606581641835543)
  ·
    refine ⟨34988171576409872462753315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23325447717606581641835543 34988171576409872462753315)
    ·
      refine ⟨52482257364614808694129973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34988171576409872462753315 52482257364614808694129973)
      ·
        refine ⟨4920211627932638315074685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52482257364614808694129973 4920211627932638315074685)
        ·
          refine ⟨1845079360474739368153007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4920211627932638315074685 1845079360474739368153007)
          ·
            refine ⟨2767619040712109052229511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1845079360474739368153007 2767619040712109052229511)
            ·
              refine ⟨4151428561068163578344267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2767619040712109052229511 4151428561068163578344267)
              ·
                refine ⟨6227142841602245367516401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4151428561068163578344267 6227142841602245367516401)
                ·
                  refine ⟨4670357131201684025637301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6227142841602245367516401 4670357131201684025637301)
                  ·
                    refine ⟨437845981050157877403497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4670357131201684025637301 437845981050157877403497)
                    ·
                      rfl

theorem cell23_2558106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 2, 5].length) (baseStart_2558106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558106 prefixEnd_2558106 := by exact prefixLift 2558106
  have htrace : WordTrace (prefixWord ++ tailWord_2558106) baseStart_2558106 baseEnd_2558106 := by
    simpa [prefixWord, tailWord_2558106, baseEnd_2558106] using wordTrace_append hprefix tailTrace_2558106
  have hstable : (prefixWord ++ tailWord_2558106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558106).length < 2 ^ (prefixWord ++ tailWord_2558106).sum := by decide
  have hdescent : baseEnd_2558106 < baseStart_2558106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558109 : List Nat := [1, 4, 2, 1, 1, 5, 1, 1, 2, 1, 4]
def baseStart_2558109 : Nat := 118140960795 + 2558109 * 2 ^ 59
def prefixEnd_2558109 : Nat := 4983230072969 + 3 ^ 40 * 2558109 * 2
def baseEnd_2558109 : Nat := 1313539483592437120472977

theorem tailTrace_2558109 : CollatzResearch.WordTrace tailWord_2558109 prefixEnd_2558109 1313539483592437120472977 := by
  unfold tailWord_2558109
  simp only [CollatzResearch.WordTrace]
  refine ⟨93301900289415458079701381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62201266859610305386467587 93301900289415458079701381)
  ·
    refine ⟨17494106304265398389944009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93301900289415458079701381 17494106304265398389944009)
    ·
      refine ⟨13120579728199048792458007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17494106304265398389944009 13120579728199048792458007)
      ·
        refine ⟨19680869592298573188687011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13120579728199048792458007 19680869592298573188687011)
        ·
          refine ⟨29521304388447859783030517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19680869592298573188687011 29521304388447859783030517)
          ·
            refine ⟨2767622286416986854659111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29521304388447859783030517 2767622286416986854659111)
            ·
              refine ⟨4151433429625480281988667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2767622286416986854659111 4151433429625480281988667)
              ·
                refine ⟨6227150144438220422983001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4151433429625480281988667 6227150144438220422983001)
                ·
                  refine ⟨4670362608328665317237251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6227150144438220422983001 4670362608328665317237251)
                  ·
                    refine ⟨7005543912492997975855877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4670362608328665317237251 7005543912492997975855877)
                    ·
                      refine ⟨1313539483592437120472977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7005543912492997975855877 1313539483592437120472977)
                      ·
                        rfl

theorem cell23_2558109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_2558109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558109 prefixEnd_2558109 := by exact prefixLift 2558109
  have htrace : WordTrace (prefixWord ++ tailWord_2558109) baseStart_2558109 baseEnd_2558109 := by
    simpa [prefixWord, tailWord_2558109, baseEnd_2558109] using wordTrace_append hprefix tailTrace_2558109
  have hstable : (prefixWord ++ tailWord_2558109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558109).length < 2 ^ (prefixWord ++ tailWord_2558109).sum := by decide
  have hdescent : baseEnd_2558109 < baseStart_2558109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558112 : List Nat := [2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 3]
def baseStart_2558112 : Nat := 118140960795 + 2558112 * 2 ^ 59
def prefixEnd_2558112 : Nat := 4983230072969 + 3 ^ 40 * 2558112 * 2
def baseEnd_2558112 : Nat := 1313541024034400608735463

theorem tailTrace_2558112 : CollatzResearch.WordTrace tailWord_2558112 prefixEnd_2558112 1313541024034400608735463 := by
  unfold tailWord_2558112
  simp only [CollatzResearch.WordTrace]
  refine ⟨46651004854202294796030295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62201339805603059728040393 46651004854202294796030295)
  ·
    refine ⟨69976507281303442194045443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46651004854202294796030295 69976507281303442194045443)
    ·
      refine ⟨104964760921955163291068165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69976507281303442194045443 104964760921955163291068165)
      ·
        refine ⟨19680892672866593117075281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104964760921955163291068165 19680892672866593117075281)
        ·
          refine ⟨14760669504649944837806461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19680892672866593117075281 14760669504649944837806461)
          ·
            refine ⟨5535251064243729314177423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14760669504649944837806461 5535251064243729314177423)
            ·
              refine ⟨8302876596365593971266135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5535251064243729314177423 8302876596365593971266135)
              ·
                refine ⟨12454314894548390956899203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8302876596365593971266135 12454314894548390956899203)
                ·
                  refine ⟨18681472341822586435348805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12454314894548390956899203 18681472341822586435348805)
                  ·
                    refine ⟨3502776064091734956627901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18681472341822586435348805 3502776064091734956627901)
                    ·
                      refine ⟨1313541024034400608735463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3502776064091734956627901 1313541024034400608735463)
                      ·
                        rfl

theorem cell23_2558112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_2558112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558112 prefixEnd_2558112 := by exact prefixLift 2558112
  have htrace : WordTrace (prefixWord ++ tailWord_2558112) baseStart_2558112 baseEnd_2558112 := by
    simpa [prefixWord, tailWord_2558112, baseEnd_2558112] using wordTrace_append hprefix tailTrace_2558112
  have hstable : (prefixWord ++ tailWord_2558112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558112).length < 2 ^ (prefixWord ++ tailWord_2558112).sum := by decide
  have hdescent : baseEnd_2558112 < baseStart_2558112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558135 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 6]
def baseStart_2558135 : Nat := 118140960795 + 2558135 * 2 ^ 59
def prefixEnd_2558135 : Nat := 4983230072969 + 3 ^ 40 * 2558135 * 2
def baseEnd_2558135 : Nat := 1313552834089454018747857

theorem tailTrace_2558135 : CollatzResearch.WordTrace tailWord_2558135 prefixEnd_2558135 1313552834089454018747857 := by
  unfold tailWord_2558135
  simp only [CollatzResearch.WordTrace]
  refine ⟨93302848587321264520147859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62201899058214176346765239 93302848587321264520147859)
  ·
    refine ⟨139954272880981896780221789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93302848587321264520147859 139954272880981896780221789)
    ·
      refine ⟨52482852330368211292583171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139954272880981896780221789 52482852330368211292583171)
      ·
        refine ⟨78724278495552316938874757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52482852330368211292583171 78724278495552316938874757)
        ·
          refine ⟨14760802217916059426039017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78724278495552316938874757 14760802217916059426039017)
          ·
            refine ⟨11070601663437044569529263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14760802217916059426039017 11070601663437044569529263)
            ·
              refine ⟨16605902495155566854293895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11070601663437044569529263 16605902495155566854293895)
              ·
                refine ⟨24908853742733350281440843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16605902495155566854293895 24908853742733350281440843)
                ·
                  refine ⟨37363280614100025422161265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24908853742733350281440843 37363280614100025422161265)
                  ·
                    refine ⟨28022460460575019066620949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37363280614100025422161265 28022460460575019066620949)
                    ·
                      refine ⟨1313552834089454018747857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28022460460575019066620949 1313552834089454018747857)
                      ·
                        rfl

theorem cell23_2558135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_2558135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558135 prefixEnd_2558135 := by exact prefixLift 2558135
  have htrace : WordTrace (prefixWord ++ tailWord_2558135) baseStart_2558135 baseEnd_2558135 := by
    simpa [prefixWord, tailWord_2558135, baseEnd_2558135] using wordTrace_append hprefix tailTrace_2558135
  have hstable : (prefixWord ++ tailWord_2558135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558135).length < 2 ^ (prefixWord ++ tailWord_2558135).sum := by decide
  have hdescent : baseEnd_2558135 < baseStart_2558135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558146 : List Nat := [3, 5, 1, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_2558146 : Nat := 118140960795 + 2558146 * 2 ^ 59
def prefixEnd_2558146 : Nat := 4983230072969 + 3 ^ 40 * 2558146 * 2
def baseEnd_2558146 : Nat := 1313558482376653475710307

theorem tailTrace_2558146 : CollatzResearch.WordTrace tailWord_2558146 prefixEnd_2558146 1313558482376653475710307 := by
  unfold tailWord_2558146
  simp only [CollatzResearch.WordTrace]
  refine ⟨23325812447570353349699573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62202166526854275599198861 23325812447570353349699573)
  ·
    refine ⟨2186794916959720626534335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23325812447570353349699573 2186794916959720626534335)
    ·
      refine ⟨3280192375439580939801503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2186794916959720626534335 3280192375439580939801503)
      ·
        refine ⟨4920288563159371409702255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3280192375439580939801503 4920288563159371409702255)
        ·
          refine ⟨7380432844739057114553383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4920288563159371409702255 7380432844739057114553383)
          ·
            refine ⟨11070649267108585671830075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7380432844739057114553383 11070649267108585671830075)
            ·
              refine ⟨16605973900662878507745113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11070649267108585671830075 16605973900662878507745113)
              ·
                refine ⟨12454480425497158880808835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16605973900662878507745113 12454480425497158880808835)
                ·
                  refine ⟨18681720638245738321213253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12454480425497158880808835 18681720638245738321213253)
                  ·
                    refine ⟨3502822619671075935227485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18681720638245738321213253 3502822619671075935227485)
                    ·
                      refine ⟨1313558482376653475710307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3502822619671075935227485 1313558482376653475710307)
                      ·
                        rfl

theorem cell23_2558146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_2558146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558146 prefixEnd_2558146 := by exact prefixLift 2558146
  have htrace : WordTrace (prefixWord ++ tailWord_2558146) baseStart_2558146 baseEnd_2558146 := by
    simpa [prefixWord, tailWord_2558146, baseEnd_2558146] using wordTrace_append hprefix tailTrace_2558146
  have hstable : (prefixWord ++ tailWord_2558146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558146).length < 2 ^ (prefixWord ++ tailWord_2558146).sum := by decide
  have hdescent : baseEnd_2558146 < baseStart_2558146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558175 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 3, 6]
def baseStart_2558175 : Nat := 118140960795 + 2558175 * 2 ^ 59
def prefixEnd_2558175 : Nat := 4983230072969 + 3 ^ 40 * 2558175 * 2
def baseEnd_2558175 : Nat := 437857791105211287415891

theorem tailTrace_2558175 : CollatzResearch.WordTrace tailWord_2558175 prefixEnd_2558175 437857791105211287415891 := by
  unfold tailWord_2558175
  simp only [CollatzResearch.WordTrace]
  refine ⟨93304307507176351351603979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62202871671450900901069319 93304307507176351351603979)
  ·
    refine ⟨139956461260764527027405969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93304307507176351351603979 139956461260764527027405969)
    ·
      refine ⟨104967345945573395270554477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139956461260764527027405969 104967345945573395270554477)
      ·
        refine ⟨39362754729590023226457929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104967345945573395270554477 39362754729590023226457929)
        ·
          refine ⟨29522066047192517419843447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39362754729590023226457929 29522066047192517419843447)
          ·
            refine ⟨44283099070788776129765171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29522066047192517419843447 44283099070788776129765171)
            ·
              refine ⟨66424648606183164194647757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44283099070788776129765171 66424648606183164194647757)
              ·
                refine ⟨24909243227318686572992909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66424648606183164194647757 24909243227318686572992909)
                ·
                  refine ⟨9340966210244507464872341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24909243227318686572992909 9340966210244507464872341)
                  ·
                    refine ⟨437857791105211287415891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9340966210244507464872341 437857791105211287415891)
                    ·
                      rfl

theorem cell23_2558175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 6].length) (baseStart_2558175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558175 prefixEnd_2558175 := by exact prefixLift 2558175
  have htrace : WordTrace (prefixWord ++ tailWord_2558175) baseStart_2558175 baseEnd_2558175 := by
    simpa [prefixWord, tailWord_2558175, baseEnd_2558175] using wordTrace_append hprefix tailTrace_2558175
  have hstable : (prefixWord ++ tailWord_2558175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558175).length < 2 ^ (prefixWord ++ tailWord_2558175).sum := by decide
  have hdescent : baseEnd_2558175 < baseStart_2558175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558185 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 5, 1, 5]
def baseStart_2558185 : Nat := 118140960795 + 2558185 * 2 ^ 59
def prefixEnd_2558185 : Nat := 4983230072969 + 3 ^ 40 * 2558185 * 2
def baseEnd_2558185 : Nat := 1313578508122178823122627

theorem tailTrace_2558185 : CollatzResearch.WordTrace tailWord_2558185 prefixEnd_2558185 1313578508122178823122627 := by
  unfold tailWord_2558185
  simp only [CollatzResearch.WordTrace]
  refine ⟨93304672237140123059468009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62203114824760082039645339 93304672237140123059468009)
  ·
    refine ⟨69978504177855092294601007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93304672237140123059468009 69978504177855092294601007)
    ·
      refine ⟨104967756266782638441901511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69978504177855092294601007 104967756266782638441901511)
      ·
        refine ⟨157451634400173957662852267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104967756266782638441901511 157451634400173957662852267)
        ·
          refine ⟨236177451600260936494278401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157451634400173957662852267 236177451600260936494278401)
          ·
            refine ⟨177133088700195702370708801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236177451600260936494278401 177133088700195702370708801)
            ·
              refine ⟨132849816525146776778031601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177133088700195702370708801 132849816525146776778031601)
              ·
                refine ⟨99637362393860082583523701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132849816525146776778031601 99637362393860082583523701)
                ·
                  refine ⟨9341002724424382742205347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99637362393860082583523701 9341002724424382742205347)
                  ·
                    refine ⟨14011504086636574113308021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9341002724424382742205347 14011504086636574113308021)
                    ·
                      refine ⟨1313578508122178823122627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14011504086636574113308021 1313578508122178823122627)
                      ·
                        rfl

theorem cell23_2558185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 1, 5].length) (baseStart_2558185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558185 prefixEnd_2558185 := by exact prefixLift 2558185
  have htrace : WordTrace (prefixWord ++ tailWord_2558185) baseStart_2558185 baseEnd_2558185 := by
    simpa [prefixWord, tailWord_2558185, baseEnd_2558185] using wordTrace_append hprefix tailTrace_2558185
  have hstable : (prefixWord ++ tailWord_2558185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558185).length < 2 ^ (prefixWord ++ tailWord_2558185).sum := by decide
  have hdescent : baseEnd_2558185 < baseStart_2558185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558195 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 6]
def baseStart_2558195 : Nat := 118140960795 + 2558195 * 2 ^ 59
def prefixEnd_2558195 : Nat := 4983230072969 + 3 ^ 40 * 2558195 * 2
def baseEnd_2558195 : Nat := 1313583642928723783997581

theorem tailTrace_2558195 : CollatzResearch.WordTrace tailWord_2558195 prefixEnd_2558195 1313583642928723783997581 := by
  unfold tailWord_2558195
  simp only [CollatzResearch.WordTrace]
  refine ⟨93305036967103894767332039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62203357978069263178221359 93305036967103894767332039)
  ·
    refine ⟨139957555450655842150998059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93305036967103894767332039 139957555450655842150998059)
    ·
      refine ⟨209936333175983763226497089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139957555450655842150998059 209936333175983763226497089)
      ·
        refine ⟨157452249881987822419872817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209936333175983763226497089 157452249881987822419872817)
        ·
          refine ⟨118089187411490866814904613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157452249881987822419872817 118089187411490866814904613)
          ·
            refine ⟨22141722639654537527794615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118089187411490866814904613 22141722639654537527794615)
            ·
              refine ⟨33212583959481806291691923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22141722639654537527794615 33212583959481806291691923)
              ·
                refine ⟨49818875939222709437537885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33212583959481806291691923 49818875939222709437537885)
                ·
                  refine ⟨18682078477208516039076707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49818875939222709437537885 18682078477208516039076707)
                  ·
                    refine ⟨28023117715812774058615061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18682078477208516039076707 28023117715812774058615061)
                    ·
                      refine ⟨1313583642928723783997581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28023117715812774058615061 1313583642928723783997581)
                      ·
                        rfl

theorem cell23_2558195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 6].length) (baseStart_2558195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558195 prefixEnd_2558195 := by exact prefixLift 2558195
  have htrace : WordTrace (prefixWord ++ tailWord_2558195) baseStart_2558195 baseEnd_2558195 := by
    simpa [prefixWord, tailWord_2558195, baseEnd_2558195] using wordTrace_append hprefix tailTrace_2558195
  have hstable : (prefixWord ++ tailWord_2558195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558195).length < 2 ^ (prefixWord ++ tailWord_2558195).sum := by decide
  have hdescent : baseEnd_2558195 < baseStart_2558195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558202 : List Nat := [3, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5]
def baseStart_2558202 : Nat := 118140960795 + 2558202 * 2 ^ 59
def prefixEnd_2558202 : Nat := 4983230072969 + 3 ^ 40 * 2558202 * 2
def baseEnd_2558202 : Nat := 1313587237293305256610049

theorem tailTrace_2558202 : CollatzResearch.WordTrace tailWord_2558202 prefixEnd_2558202 1313587237293305256610049 := by
  unfold tailWord_2558202
  simp only [CollatzResearch.WordTrace]
  refine ⟨23326323069519633740709215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62203528185385689975224573 23326323069519633740709215)
  ·
    refine ⟨34989484604279450611063823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23326323069519633740709215 34989484604279450611063823)
    ·
      refine ⟨52484226906419175916595735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34989484604279450611063823 52484226906419175916595735)
      ·
        refine ⟨78726340359628763874893603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52484226906419175916595735 78726340359628763874893603)
        ·
          refine ⟨118089510539443145812340405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78726340359628763874893603 118089510539443145812340405)
          ·
            refine ⟨11070891613072794919906913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 118089510539443145812340405 11070891613072794919906913)
            ·
              refine ⟨8303168709804596189930185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11070891613072794919906913 8303168709804596189930185)
              ·
                refine ⟨6227376532353447142447639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8303168709804596189930185 6227376532353447142447639)
                ·
                  refine ⟨9341064798530170713671459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6227376532353447142447639 9341064798530170713671459)
                  ·
                    refine ⟨14011597197795256070507189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9341064798530170713671459 14011597197795256070507189)
                    ·
                      refine ⟨1313587237293305256610049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14011597197795256070507189 1313587237293305256610049)
                      ·
                        rfl

theorem cell23_2558202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_2558202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558202 prefixEnd_2558202 := by exact prefixLift 2558202
  have htrace : WordTrace (prefixWord ++ tailWord_2558202) baseStart_2558202 baseEnd_2558202 := by
    simpa [prefixWord, tailWord_2558202, baseEnd_2558202] using wordTrace_append hprefix tailTrace_2558202
  have hstable : (prefixWord ++ tailWord_2558202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558202).length < 2 ^ (prefixWord ++ tailWord_2558202).sum := by decide
  have hdescent : baseEnd_2558202 < baseStart_2558202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558209 : List Nat := [1, 2, 4, 1, 1, 2, 3, 3, 2, 4]
def baseStart_2558209 : Nat := 118140960795 + 2558209 * 2 ^ 59
def prefixEnd_2558209 : Nat := 4983230072969 + 3 ^ 40 * 2558209 * 2
def baseEnd_2558209 : Nat := 437863610552628909740839

theorem tailTrace_2558209 : CollatzResearch.WordTrace tailWord_2558209 prefixEnd_2558209 437863610552628909740839 := by
  unfold tailWord_2558209
  simp only [CollatzResearch.WordTrace]
  refine ⟨93305547589053175158341681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62203698392702116772227787 93305547589053175158341681)
  ·
    refine ⟨69979160691789881368756261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93305547589053175158341681 69979160691789881368756261)
    ·
      refine ⟨13121092629710602756641799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69979160691789881368756261 13121092629710602756641799)
      ·
        refine ⟨19681638944565904134962699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13121092629710602756641799 19681638944565904134962699)
        ·
          refine ⟨29522458416848856202444049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19681638944565904134962699 29522458416848856202444049)
          ·
            refine ⟨22141843812636642151833037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29522458416848856202444049 22141843812636642151833037)
            ·
              refine ⟨8303191429738740806937389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22141843812636642151833037 8303191429738740806937389)
              ·
                refine ⟨3113696786152027802601521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8303191429738740806937389 3113696786152027802601521)
                ·
                  refine ⟨2335272589614020851951141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3113696786152027802601521 2335272589614020851951141)
                  ·
                    refine ⟨437863610552628909740839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2335272589614020851951141 437863610552628909740839)
                    ·
                      rfl

theorem cell23_2558209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_2558209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558209 prefixEnd_2558209 := by exact prefixLift 2558209
  have htrace : WordTrace (prefixWord ++ tailWord_2558209) baseStart_2558209 baseEnd_2558209 := by
    simpa [prefixWord, tailWord_2558209, baseEnd_2558209] using wordTrace_append hprefix tailTrace_2558209
  have hstable : (prefixWord ++ tailWord_2558209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558209).length < 2 ^ (prefixWord ++ tailWord_2558209).sum := by decide
  have hdescent : baseEnd_2558209 < baseStart_2558209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558216 : List Nat := [2, 1, 3, 2, 3, 3, 1, 2, 1, 1, 4]
def baseStart_2558216 : Nat := 118140960795 + 2558216 * 2 ^ 59
def prefixEnd_2558216 : Nat := 4983230072969 + 3 ^ 40 * 2558216 * 2
def baseEnd_2558216 : Nat := 1313594426022468201834985

theorem tailTrace_2558216 : CollatzResearch.WordTrace tailWord_2558216 prefixEnd_2558216 1313594426022468201834985 := by
  unfold tailWord_2558216
  simp only [CollatzResearch.WordTrace]
  refine ⟨46652901450013907676923251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62203868600018543569231001 46652901450013907676923251)
  ·
    refine ⟨69979352175020861515384877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46652901450013907676923251 69979352175020861515384877)
    ·
      refine ⟨26242257065632823068269329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69979352175020861515384877 26242257065632823068269329)
      ·
        refine ⟨19681692799224617301201997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26242257065632823068269329 19681692799224617301201997)
        ·
          refine ⟨7380634799709231487950749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19681692799224617301201997 7380634799709231487950749)
          ·
            refine ⟨2767738049890961807981531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7380634799709231487950749 2767738049890961807981531)
            ·
              refine ⟨4151607074836442711972297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2767738049890961807981531 4151607074836442711972297)
              ·
                refine ⟨3113705306127332033979223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4151607074836442711972297 3113705306127332033979223)
                ·
                  refine ⟨4670557959190998050968835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3113705306127332033979223 4670557959190998050968835)
                  ·
                    refine ⟨7005836938786497076453253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4670557959190998050968835 7005836938786497076453253)
                    ·
                      refine ⟨1313594426022468201834985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7005836938786497076453253 1313594426022468201834985)
                      ·
                        rfl

theorem cell23_2558216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_2558216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558216 prefixEnd_2558216 := by exact prefixLift 2558216
  have htrace : WordTrace (prefixWord ++ tailWord_2558216) baseStart_2558216 baseEnd_2558216 := by
    simpa [prefixWord, tailWord_2558216, baseEnd_2558216] using wordTrace_append hprefix tailTrace_2558216
  have hstable : (prefixWord ++ tailWord_2558216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558216).length < 2 ^ (prefixWord ++ tailWord_2558216).sum := by decide
  have hdescent : baseEnd_2558216 < baseStart_2558216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558259 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 5, 3, 2]
def baseStart_2558259 : Nat := 118140960795 + 2558259 * 2 ^ 59
def prefixEnd_2558259 : Nat := 4983230072969 + 3 ^ 40 * 2558259 * 2
def baseEnd_2558259 : Nat := 1313616505690611533597287

theorem tailTrace_2558259 : CollatzResearch.WordTrace tailWord_2558259 prefixEnd_2558259 1313616505690611533597287 := by
  unfold tailWord_2558259
  simp only [CollatzResearch.WordTrace]
  refine ⟨93307371238872033697661831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62204914159248022465107887 93307371238872033697661831)
  ·
    refine ⟨139961056858308050546492747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93307371238872033697661831 139961056858308050546492747)
    ·
      refine ⟨209941585287462075819739121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139961056858308050546492747 209941585287462075819739121)
      ·
        refine ⟨157456188965596556864804341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209941585287462075819739121 157456188965596556864804341)
        ·
          refine ⟨14761517715524677206075407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 157456188965596556864804341 14761517715524677206075407)
          ·
            refine ⟨22142276573287015809113111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14761517715524677206075407 22142276573287015809113111)
            ·
              refine ⟨33213414859930523713669667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22142276573287015809113111 33213414859930523713669667)
              ·
                refine ⟨49820122289895785570504501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33213414859930523713669667 49820122289895785570504501)
                ·
                  refine ⟨4670636464677729897234797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49820122289895785570504501 4670636464677729897234797)
                  ·
                    refine ⟨1751488674254148711463049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4670636464677729897234797 1751488674254148711463049)
                    ·
                      refine ⟨1313616505690611533597287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1751488674254148711463049 1313616505690611533597287)
                      ·
                        rfl

theorem cell23_2558259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 3, 2].length) (baseStart_2558259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558259 prefixEnd_2558259 := by exact prefixLift 2558259
  have htrace : WordTrace (prefixWord ++ tailWord_2558259) baseStart_2558259 baseEnd_2558259 := by
    simpa [prefixWord, tailWord_2558259, baseEnd_2558259] using wordTrace_append hprefix tailTrace_2558259
  have hstable : (prefixWord ++ tailWord_2558259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558259).length < 2 ^ (prefixWord ++ tailWord_2558259).sum := by decide
  have hdescent : baseEnd_2558259 < baseStart_2558259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558266 : List Nat := [3, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3]
def baseStart_2558266 : Nat := 118140960795 + 2558266 * 2 ^ 59
def prefixEnd_2558266 : Nat := 4983230072969 + 3 ^ 40 * 2558266 * 2
def baseEnd_2558266 : Nat := 1313620100055193006209755

theorem tailTrace_2558266 : CollatzResearch.WordTrace tailWord_2558266 prefixEnd_2558266 1313620100055193006209755 := by
  unfold tailWord_2558266
  simp only [CollatzResearch.WordTrace]
  refine ⟨23326906637461668473291663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62205084366564449262111101 23326906637461668473291663)
  ·
    refine ⟨34990359956192502709937495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23326906637461668473291663 34990359956192502709937495)
    ·
      refine ⟨52485539934288754064906243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34990359956192502709937495 52485539934288754064906243)
      ·
        refine ⟨78728309901433131097359365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52485539934288754064906243 78728309901433131097359365)
        ·
          refine ⟨14761558106518712080754881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78728309901433131097359365 14761558106518712080754881)
          ·
            refine ⟨11071168579889034060566161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14761558106518712080754881 11071168579889034060566161)
            ·
              refine ⟨8303376434916775545424621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11071168579889034060566161 8303376434916775545424621)
              ·
                refine ⟨3113766163093790829534233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8303376434916775545424621 3113766163093790829534233)
                ·
                  refine ⟨2335324622320343122150675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3113766163093790829534233 2335324622320343122150675)
                  ·
                    refine ⟨3502986933480514683226013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2335324622320343122150675 3502986933480514683226013)
                    ·
                      refine ⟨1313620100055193006209755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3502986933480514683226013 1313620100055193006209755)
                      ·
                        rfl

theorem cell23_2558266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3].length) (baseStart_2558266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558266 prefixEnd_2558266 := by exact prefixLift 2558266
  have htrace : WordTrace (prefixWord ++ tailWord_2558266) baseStart_2558266 baseEnd_2558266 := by
    simpa [prefixWord, tailWord_2558266, baseEnd_2558266] using wordTrace_append hprefix tailTrace_2558266
  have hstable : (prefixWord ++ tailWord_2558266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558266).length < 2 ^ (prefixWord ++ tailWord_2558266).sum := by decide
  have hdescent : baseEnd_2558266 < baseStart_2558266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558293 : List Nat := [1, 3, 2, 2, 4, 1, 1, 3, 1, 3, 2]
def baseStart_2558293 : Nat := 118140960795 + 2558293 * 2 ^ 59
def prefixEnd_2558293 : Nat := 4983230072969 + 3 ^ 40 * 2558293 * 2
def baseEnd_2558293 : Nat := 1313633964032864400572131

theorem tailTrace_2558293 : CollatzResearch.WordTrace tailWord_2558293 prefixEnd_2558293 1313633964032864400572131 := by
  unfold tailWord_2558293
  simp only [CollatzResearch.WordTrace]
  refine ⟨93308611320748857504399533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62205740880499238336266355 93308611320748857504399533)
  ·
    refine ⟨34990729245280821564149825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93308611320748857504399533 34990729245280821564149825)
    ·
      refine ⟨26243046933960616173112369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34990729245280821564149825 26243046933960616173112369)
      ·
        refine ⟨19682285200470462129834277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26243046933960616173112369 19682285200470462129834277)
        ·
          refine ⟨3690428475088211649343927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19682285200470462129834277 3690428475088211649343927)
          ·
            refine ⟨5535642712632317474015891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3690428475088211649343927 5535642712632317474015891)
            ·
              refine ⟨8303464068948476211023837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5535642712632317474015891 8303464068948476211023837)
              ·
                refine ⟨3113799025855678579133939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8303464068948476211023837 3113799025855678579133939)
                ·
                  refine ⟨4670698538783517868700909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3113799025855678579133939 4670698538783517868700909)
                  ·
                    refine ⟨1751511952043819200762841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4670698538783517868700909 1751511952043819200762841)
                    ·
                      refine ⟨1313633964032864400572131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1751511952043819200762841 1313633964032864400572131)
                      ·
                        rfl

theorem cell23_2558293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_2558293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558293 prefixEnd_2558293 := by exact prefixLift 2558293
  have htrace : WordTrace (prefixWord ++ tailWord_2558293) baseStart_2558293 baseEnd_2558293 := by
    simpa [prefixWord, tailWord_2558293, baseEnd_2558293] using wordTrace_append hprefix tailTrace_2558293
  have hstable : (prefixWord ++ tailWord_2558293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558293).length < 2 ^ (prefixWord ++ tailWord_2558293).sum := by decide
  have hdescent : baseEnd_2558293 < baseStart_2558293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558392 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 1, 3, 6]
def baseStart_2558392 : Nat := 118140960795 + 2558392 * 2 ^ 59
def prefixEnd_2558392 : Nat := 4983230072969 + 3 ^ 40 * 2558392 * 2
def baseEnd_2558392 : Nat := 1313684798617659513234175

theorem tailTrace_2558392 : CollatzResearch.WordTrace tailWord_2558392 prefixEnd_2558392 1313684798617659513234175 := by
  unfold tailWord_2558392
  simp only [CollatzResearch.WordTrace]
  refine ⟨46656111073695098706126715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62208148098260131608168953 46656111073695098706126715)
  ·
    refine ⟨69984166610542648059190073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46656111073695098706126715 69984166610542648059190073)
    ·
      refine ⟨52488124957906986044392555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69984166610542648059190073 52488124957906986044392555)
      ·
        refine ⟨78732187436860479066588833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52488124957906986044392555 78732187436860479066588833)
        ·
          refine ⟨59049140577645359299941625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78732187436860479066588833 59049140577645359299941625)
          ·
            refine ⟨44286855433234019474956219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59049140577645359299941625 44286855433234019474956219)
            ·
              refine ⟨66430283149851029212434329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44286855433234019474956219 66430283149851029212434329)
              ·
                refine ⟨49822712362388271909325747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66430283149851029212434329 49822712362388271909325747)
                ·
                  refine ⟨74734068543582407863988621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49822712362388271909325747 74734068543582407863988621)
                  ·
                    refine ⟨28025275703843402948995733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74734068543582407863988621 28025275703843402948995733)
                    ·
                      refine ⟨1313684798617659513234175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28025275703843402948995733 1313684798617659513234175)
                      ·
                        rfl

theorem cell23_2558392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_2558392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558392 prefixEnd_2558392 := by exact prefixLift 2558392
  have htrace : WordTrace (prefixWord ++ tailWord_2558392) baseStart_2558392 baseEnd_2558392 := by
    simpa [prefixWord, tailWord_2558392, baseEnd_2558392] using wordTrace_append hprefix tailTrace_2558392
  have hstable : (prefixWord ++ tailWord_2558392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558392).length < 2 ^ (prefixWord ++ tailWord_2558392).sum := by decide
  have hdescent : baseEnd_2558392 < baseStart_2558392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558396 : List Nat := [2, 2, 2, 4, 1, 1, 1, 3, 2, 1, 4]
def baseStart_2558396 : Nat := 118140960795 + 2558396 * 2 ^ 59
def prefixEnd_2558396 : Nat := 4983230072969 + 3 ^ 40 * 2558396 * 2
def baseEnd_2558396 : Nat := 1313686852540277497584157

theorem tailTrace_2558396 : CollatzResearch.WordTrace tailWord_2558396 prefixEnd_2558396 1313686852540277497584157 := by
  unfold tailWord_2558396
  simp only [CollatzResearch.WordTrace]
  refine ⟨46656184019687853047699521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62208245359583804063599361 46656184019687853047699521)
  ·
    refine ⟨34992138014765889785774641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46656184019687853047699521 34992138014765889785774641)
    ·
      refine ⟨26244103511074417339330981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34992138014765889785774641 26244103511074417339330981)
      ·
        refine ⟨4920769408326453251124559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26244103511074417339330981 4920769408326453251124559)
        ·
          refine ⟨7381154112489679876686839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4920769408326453251124559 7381154112489679876686839)
          ·
            refine ⟨11071731168734519815030259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7381154112489679876686839 11071731168734519815030259)
            ·
              refine ⟨16607596753101779722545389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11071731168734519815030259 16607596753101779722545389)
              ·
                refine ⟨6227848782413167395954521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16607596753101779722545389 6227848782413167395954521)
                ·
                  refine ⟨4670886586809875546965891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6227848782413167395954521 4670886586809875546965891)
                  ·
                    refine ⟨7006329880214813320448837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4670886586809875546965891 7006329880214813320448837)
                    ·
                      refine ⟨1313686852540277497584157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7006329880214813320448837 1313686852540277497584157)
                      ·
                        rfl

theorem cell23_2558396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_2558396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558396 prefixEnd_2558396 := by exact prefixLift 2558396
  have htrace : WordTrace (prefixWord ++ tailWord_2558396) baseStart_2558396 baseEnd_2558396 := by
    simpa [prefixWord, tailWord_2558396, baseEnd_2558396] using wordTrace_append hprefix tailTrace_2558396
  have hstable : (prefixWord ++ tailWord_2558396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558396).length < 2 ^ (prefixWord ++ tailWord_2558396).sum := by decide
  have hdescent : baseEnd_2558396 < baseStart_2558396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558449 : List Nat := [1, 2, 2, 2, 3, 1, 1, 3, 3, 5]
def baseStart_2558449 : Nat := 118140960795 + 2558449 * 2 ^ 59
def prefixEnd_2558449 : Nat := 4983230072969 + 3 ^ 40 * 2558449 * 2
def baseEnd_2558449 : Nat := 437904689004988596740471

theorem tailTrace_2558449 : CollatzResearch.WordTrace tailWord_2558449 prefixEnd_2558449 437904689004988596740471 := by
  unfold tailWord_2558449
  simp only [CollatzResearch.WordTrace]
  refine ⟨93314301108183696147078401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62209534072122464098052267 93314301108183696147078401)
  ·
    refine ⟨69985725831137772110308801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93314301108183696147078401 69985725831137772110308801)
    ·
      refine ⟨52489294373353329082731601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69985725831137772110308801 52489294373353329082731601)
      ·
        refine ⟨39366970780014996812048701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52489294373353329082731601 39366970780014996812048701)
        ·
          refine ⟨14762614042505623804518263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39366970780014996812048701 14762614042505623804518263)
          ·
            refine ⟨22143921063758435706777395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14762614042505623804518263 22143921063758435706777395)
            ·
              refine ⟨33215881595637653560166093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22143921063758435706777395 33215881595637653560166093)
              ·
                refine ⟨12455955598364120085062285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33215881595637653560166093 12455955598364120085062285)
                ·
                  refine ⟨4670983349386545031898357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12455955598364120085062285 4670983349386545031898357)
                  ·
                    refine ⟨437904689004988596740471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4670983349386545031898357 437904689004988596740471)
                    ·
                      rfl

theorem cell23_2558449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 5].length) (baseStart_2558449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558449 prefixEnd_2558449 := by exact prefixLift 2558449
  have htrace : WordTrace (prefixWord ++ tailWord_2558449) baseStart_2558449 baseEnd_2558449 := by
    simpa [prefixWord, tailWord_2558449, baseEnd_2558449] using wordTrace_append hprefix tailTrace_2558449
  have hstable : (prefixWord ++ tailWord_2558449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558449).length < 2 ^ (prefixWord ++ tailWord_2558449).sum := by decide
  have hdescent : baseEnd_2558449 < baseStart_2558449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558450 : List Nat := [3, 2, 1, 4, 2, 2, 1, 1, 2, 2, 3]
def baseStart_2558450 : Nat := 118140960795 + 2558450 * 2 ^ 59
def prefixEnd_2558450 : Nat := 4983230072969 + 3 ^ 40 * 2558450 * 2
def baseEnd_2558450 : Nat := 1313714580495620286308909

theorem tailTrace_2558450 : CollatzResearch.WordTrace tailWord_2558450 prefixEnd_2558450 1313714580495620286308909 := by
  unfold tailWord_2558450
  simp only [CollatzResearch.WordTrace]
  refine ⟨23328584395295018329466201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62209558387453382211909869 23328584395295018329466201)
  ·
    refine ⟨17496438296471263747099651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23328584395295018329466201 17496438296471263747099651)
    ·
      refine ⟨26244657444706895620649477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17496438296471263747099651 26244657444706895620649477)
      ·
        refine ⟨4920873270882542928871777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26244657444706895620649477 4920873270882542928871777)
        ·
          refine ⟨3690654953161907196653833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4920873270882542928871777 3690654953161907196653833)
          ·
            refine ⟨2767991214871430397490375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3690654953161907196653833 2767991214871430397490375)
            ·
              refine ⟨4151986822307145596235563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2767991214871430397490375 4151986822307145596235563)
              ·
                refine ⟨6227980233460718394353345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4151986822307145596235563 6227980233460718394353345)
                ·
                  refine ⟨4670985175095538795765009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6227980233460718394353345 4670985175095538795765009)
                  ·
                    refine ⟨3503238881321654096823757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4670985175095538795765009 3503238881321654096823757)
                    ·
                      refine ⟨1313714580495620286308909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3503238881321654096823757 1313714580495620286308909)
                      ·
                        rfl

theorem cell23_2558450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_2558450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558450 prefixEnd_2558450 := by exact prefixLift 2558450
  have htrace : WordTrace (prefixWord ++ tailWord_2558450) baseStart_2558450 baseEnd_2558450 := by
    simpa [prefixWord, tailWord_2558450, baseEnd_2558450] using wordTrace_append hprefix tailTrace_2558450
  have hstable : (prefixWord ++ tailWord_2558450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558450).length < 2 ^ (prefixWord ++ tailWord_2558450).sum := by decide
  have hdescent : baseEnd_2558450 < baseStart_2558450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558456 : List Nat := [2, 1, 2, 1, 1, 4, 3, 1, 1, 5, 2]
def baseStart_2558456 : Nat := 118140960795 + 2558456 * 2 ^ 59
def prefixEnd_2558456 : Nat := 4983230072969 + 3 ^ 40 * 2558456 * 2
def baseEnd_2558456 : Nat := 1313717661379547262833881

theorem tailTrace_2558456 : CollatzResearch.WordTrace tailWord_2558456 prefixEnd_2558456 1313717661379547262833881 := by
  unfold tailWord_2558456
  simp only [CollatzResearch.WordTrace]
  refine ⟨46657278209579168171291611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62209704279438890895055481 46657278209579168171291611)
  ·
    refine ⟨69985917314368752256937417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46657278209579168171291611 69985917314368752256937417)
    ·
      refine ⟨52489437985776564192703063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69985917314368752256937417 52489437985776564192703063)
      ·
        refine ⟨78734156978664846289054595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52489437985776564192703063 78734156978664846289054595)
        ·
          refine ⟨118101235467997269433581893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78734156978664846289054595 118101235467997269433581893)
          ·
            refine ⟨22143981650249488018796605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118101235467997269433581893 22143981650249488018796605)
            ·
              refine ⟨8303993118843558007048727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22143981650249488018796605 8303993118843558007048727)
              ·
                refine ⟨12455989678265337010573091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8303993118843558007048727 12455989678265337010573091)
                ·
                  refine ⟨18683984517398005515859637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12455989678265337010573091 18683984517398005515859637)
                  ·
                    refine ⟨1751623548506063017111841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18683984517398005515859637 1751623548506063017111841)
                    ·
                      refine ⟨1313717661379547262833881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1751623548506063017111841 1313717661379547262833881)
                      ·
                        rfl

theorem cell23_2558456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 1, 5, 2].length) (baseStart_2558456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558456 prefixEnd_2558456 := by exact prefixLift 2558456
  have htrace : WordTrace (prefixWord ++ tailWord_2558456) baseStart_2558456 baseEnd_2558456 := by
    simpa [prefixWord, tailWord_2558456, baseEnd_2558456] using wordTrace_append hprefix tailTrace_2558456
  have hstable : (prefixWord ++ tailWord_2558456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558456).length < 2 ^ (prefixWord ++ tailWord_2558456).sum := by decide
  have hdescent : baseEnd_2558456 < baseStart_2558456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558470 : List Nat := [6, 2, 1, 1, 1, 2, 1, 1, 8]
def baseStart_2558470 : Nat := 118140960795 + 2558470 * 2 ^ 59
def prefixEnd_2558470 : Nat := 4983230072969 + 3 ^ 40 * 2558470 * 2
def baseEnd_2558470 : Nat := 145969427789856689784313

theorem tailTrace_2558470 : CollatzResearch.WordTrace tailWord_2558470 prefixEnd_2558470 145969427789856689784313 := by
  unfold tailWord_2558470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2916095845034613022924777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 62210044694071744489061909 2916095845034613022924777)
  ·
    refine ⟨2187071883775959767193583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2916095845034613022924777 2187071883775959767193583)
    ·
      refine ⟨3280607825663939650790375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2187071883775959767193583 3280607825663939650790375)
      ·
        refine ⟨4920911738495909476185563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3280607825663939650790375 4920911738495909476185563)
        ·
          refine ⟨7381367607743864214278345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4920911738495909476185563 7381367607743864214278345)
          ·
            refine ⟨5536025705807898160708759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7381367607743864214278345 5536025705807898160708759)
            ·
              refine ⟨8304038558711847241063139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5536025705807898160708759 8304038558711847241063139)
              ·
                refine ⟨12456057838067770861594709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8304038558711847241063139 12456057838067770861594709)
                ·
                  refine ⟨145969427789856689784313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12456057838067770861594709 145969427789856689784313)
                  ·
                    rfl

theorem cell23_2558470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_2558470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558470 prefixEnd_2558470 := by exact prefixLift 2558470
  have htrace : WordTrace (prefixWord ++ tailWord_2558470) baseStart_2558470 baseEnd_2558470 := by
    simpa [prefixWord, tailWord_2558470, baseEnd_2558470] using wordTrace_append hprefix tailTrace_2558470
  have hstable : (prefixWord ++ tailWord_2558470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558470).length < 2 ^ (prefixWord ++ tailWord_2558470).sum := by decide
  have hdescent : baseEnd_2558470 < baseStart_2558470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558489 : List Nat := [1, 2, 1, 2, 1, 1, 2, 6, 1, 1, 5]
def baseStart_2558489 : Nat := 118140960795 + 2558489 * 2 ^ 59
def prefixEnd_2558489 : Nat := 4983230072969 + 3 ^ 40 * 2558489 * 2
def baseEnd_2558489 : Nat := 1313734606241145633721229

theorem tailTrace_2558489 : CollatzResearch.WordTrace tailWord_2558489 prefixEnd_2558489 1313734606241145633721229 := by
  unfold tailWord_2558489
  simp only [CollatzResearch.WordTrace]
  refine ⟨93315760028038782978534521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62210506685359188652356347 93315760028038782978534521)
  ·
    refine ⟨69986820021029087233900891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93315760028038782978534521 69986820021029087233900891)
    ·
      refine ⟨104980230031543630850851337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69986820021029087233900891 104980230031543630850851337)
      ·
        refine ⟨78735172523657723138138503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104980230031543630850851337 78735172523657723138138503)
        ·
          refine ⟨118102758785486584707207755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78735172523657723138138503 118102758785486584707207755)
          ·
            refine ⟨177154138178229877060811633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118102758785486584707207755 177154138178229877060811633)
            ·
              refine ⟨132865603633672407795608725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177154138178229877060811633 132865603633672407795608725)
              ·
                refine ⟨6228075170328394115419159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 132865603633672407795608725 6228075170328394115419159)
                ·
                  refine ⟨9342112755492591173128739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6228075170328394115419159 9342112755492591173128739)
                  ·
                    refine ⟨14013169133238886759693109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9342112755492591173128739 14013169133238886759693109)
                    ·
                      refine ⟨1313734606241145633721229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14013169133238886759693109 1313734606241145633721229)
                      ·
                        rfl

theorem cell23_2558489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_2558489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558489 prefixEnd_2558489 := by exact prefixLift 2558489
  have htrace : WordTrace (prefixWord ++ tailWord_2558489) baseStart_2558489 baseEnd_2558489 := by
    simpa [prefixWord, tailWord_2558489, baseEnd_2558489] using wordTrace_append hprefix tailTrace_2558489
  have hstable : (prefixWord ++ tailWord_2558489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558489).length < 2 ^ (prefixWord ++ tailWord_2558489).sum := by decide
  have hdescent : baseEnd_2558489 < baseStart_2558489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558500 : List Nat := [2, 3, 1, 5, 1, 1, 2, 2, 1, 5]
def baseStart_2558500 : Nat := 118140960795 + 2558500 * 2 ^ 59
def prefixEnd_2558500 : Nat := 4983230072969 + 3 ^ 40 * 2558500 * 2
def baseEnd_2558500 : Nat := 437913418176115030227893

theorem tailTrace_2558500 : CollatzResearch.WordTrace tailWord_2558500 prefixEnd_2558500 437913418176115030227893 := by
  unfold tailWord_2558500
  simp only [CollatzResearch.WordTrace]
  refine ⟨46658080615499465928592477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62210774153999287904789969 46658080615499465928592477)
  ·
    refine ⟨17496780230812299723222179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46658080615499465928592477 17496780230812299723222179)
    ·
      refine ⟨26245170346218449584833269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17496780230812299723222179 26245170346218449584833269)
      ·
        refine ⟨2460484719957979648578119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26245170346218449584833269 2460484719957979648578119)
        ·
          refine ⟨3690727079936969472867179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2460484719957979648578119 3690727079936969472867179)
          ·
            refine ⟨5536090619905454209300769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3690727079936969472867179 5536090619905454209300769)
            ·
              refine ⟨4152067964929090656975577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5536090619905454209300769 4152067964929090656975577)
              ·
                refine ⟨3114050973696817992731683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4152067964929090656975577 3114050973696817992731683)
                ·
                  refine ⟨4671076460545226989097525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3114050973696817992731683 4671076460545226989097525)
                  ·
                    refine ⟨437913418176115030227893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4671076460545226989097525 437913418176115030227893)
                    ·
                      rfl

theorem cell23_2558500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_2558500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558500 prefixEnd_2558500 := by exact prefixLift 2558500
  have htrace : WordTrace (prefixWord ++ tailWord_2558500) baseStart_2558500 baseEnd_2558500 := by
    simpa [prefixWord, tailWord_2558500, baseEnd_2558500] using wordTrace_append hprefix tailTrace_2558500
  have hstable : (prefixWord ++ tailWord_2558500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558500).length < 2 ^ (prefixWord ++ tailWord_2558500).sum := by decide
  have hdescent : baseEnd_2558500 < baseStart_2558500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558563 : List Nat := [1, 1, 1, 5, 1, 2, 3, 1, 3, 3, 2]
def baseStart_2558563 : Nat := 118140960795 + 2558563 * 2 ^ 59
def prefixEnd_2558563 : Nat := 4983230072969 + 3 ^ 40 * 2558563 * 2
def baseEnd_2558563 : Nat := 1313772603809578344195889

theorem tailTrace_2558563 : CollatzResearch.WordTrace tailWord_2558563 prefixEnd_2558563 1313772603809578344195889 := by
  unfold tailWord_2558563
  simp only [CollatzResearch.WordTrace]
  refine ⟨93318459029770693616728343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62212306019847129077818895 93318459029770693616728343)
  ·
    refine ⟨139977688544656040425092515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93318459029770693616728343 139977688544656040425092515)
    ·
      refine ⟨209966532816984060637638773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139977688544656040425092515 209966532816984060637638773)
      ·
        refine ⟨19684362451592255684778635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 209966532816984060637638773 19684362451592255684778635)
        ·
          refine ⟨29526543677388383527167953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19684362451592255684778635 29526543677388383527167953)
          ·
            refine ⟨22144907758041287645375965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29526543677388383527167953 22144907758041287645375965)
            ·
              refine ⟨8304340409265482867015987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22144907758041287645375965 8304340409265482867015987)
              ·
                refine ⟨12456510613898224300523981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8304340409265482867015987 12456510613898224300523981)
                ·
                  refine ⟨4671191480211834112696493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12456510613898224300523981 4671191480211834112696493)
                  ·
                    refine ⟨1751696805079437792261185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4671191480211834112696493 1751696805079437792261185)
                    ·
                      refine ⟨1313772603809578344195889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1751696805079437792261185 1313772603809578344195889)
                      ·
                        rfl

theorem cell23_2558563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_2558563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558563 prefixEnd_2558563 := by exact prefixLift 2558563
  have htrace : WordTrace (prefixWord ++ tailWord_2558563) baseStart_2558563 baseEnd_2558563 := by
    simpa [prefixWord, tailWord_2558563, baseEnd_2558563] using wordTrace_append hprefix tailTrace_2558563
  have hstable : (prefixWord ++ tailWord_2558563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558563).length < 2 ^ (prefixWord ++ tailWord_2558563).sum := by decide
  have hdescent : baseEnd_2558563 < baseStart_2558563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558569 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 4, 6]
def baseStart_2558569 : Nat := 118140960795 + 2558569 * 2 ^ 59
def prefixEnd_2558569 : Nat := 4983230072969 + 3 ^ 40 * 2558569 * 2
def baseEnd_2558569 : Nat := 437925228231168440240287

theorem tailTrace_2558569 : CollatzResearch.WordTrace tailWord_2558569 prefixEnd_2558569 437925228231168440240287 := by
  unfold tailWord_2558569
  simp only [CollatzResearch.WordTrace]
  refine ⟨93318677867748956641446761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62212451911832637760964507 93318677867748956641446761)
  ·
    refine ⟨69989008400811717481085071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93318677867748956641446761 69989008400811717481085071)
    ·
      refine ⟨104983512601217576221627607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69989008400811717481085071 104983512601217576221627607)
      ·
        refine ⟨157475268901826364332441411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104983512601217576221627607 157475268901826364332441411)
        ·
          refine ⟨236212903352739546498662117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157475268901826364332441411 236212903352739546498662117)
          ·
            refine ⟨44289919378638664968499147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 236212903352739546498662117 44289919378638664968499147)
            ·
              refine ⟨66434879067957997452748721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44289919378638664968499147 66434879067957997452748721)
              ·
                refine ⟨49826159300968498089561541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66434879067957997452748721 49826159300968498089561541)
                ·
                  refine ⟨9342404868931593391792789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49826159300968498089561541 9342404868931593391792789)
                  ·
                    refine ⟨437925228231168440240287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9342404868931593391792789 437925228231168440240287)
                    ·
                      rfl

theorem cell23_2558569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 6].length) (baseStart_2558569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558569 prefixEnd_2558569 := by exact prefixLift 2558569
  have htrace : WordTrace (prefixWord ++ tailWord_2558569) baseStart_2558569 baseEnd_2558569 := by
    simpa [prefixWord, tailWord_2558569, baseEnd_2558569] using wordTrace_append hprefix tailTrace_2558569
  have hstable : (prefixWord ++ tailWord_2558569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558569).length < 2 ^ (prefixWord ++ tailWord_2558569).sum := by decide
  have hdescent : baseEnd_2558569 < baseStart_2558569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558579 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 5]
def baseStart_2558579 : Nat := 118140960795 + 2558579 * 2 ^ 59
def prefixEnd_2558579 : Nat := 4983230072969 + 3 ^ 40 * 2558579 * 2
def baseEnd_2558579 : Nat := 1313780819500050281595815

theorem tailTrace_2558579 : CollatzResearch.WordTrace tailWord_2558579 prefixEnd_2558579 1313780819500050281595815 := by
  unfold tailWord_2558579
  simp only [CollatzResearch.WordTrace]
  refine ⟨93319042597712728349310791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62212695065141818899540527 93319042597712728349310791)
  ·
    refine ⟨139978563896569092523966187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93319042597712728349310791 139978563896569092523966187)
    ·
      refine ⟨209967845844853638785949281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139978563896569092523966187 209967845844853638785949281)
      ·
        refine ⟨157475884383640229089461961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209967845844853638785949281 157475884383640229089461961)
        ·
          refine ⟨118106913287730171817096471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157475884383640229089461961 118106913287730171817096471)
          ·
            refine ⟨177160369931595257725644707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118106913287730171817096471 177160369931595257725644707)
            ·
              refine ⟨265740554897392886588467061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177160369931595257725644707 265740554897392886588467061)
              ·
                refine ⟨24913177021630583117668787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 265740554897392886588467061 24913177021630583117668787)
                ·
                  refine ⟨37369765532445874676503181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24913177021630583117668787 37369765532445874676503181)
                  ·
                    refine ⟨14013662074667203003688693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37369765532445874676503181 14013662074667203003688693)
                    ·
                      refine ⟨1313780819500050281595815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14013662074667203003688693 1313780819500050281595815)
                      ·
                        rfl

theorem cell23_2558579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 5].length) (baseStart_2558579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558579 prefixEnd_2558579 := by exact prefixLift 2558579
  have htrace : WordTrace (prefixWord ++ tailWord_2558579) baseStart_2558579 baseEnd_2558579 := by
    simpa [prefixWord, tailWord_2558579, baseEnd_2558579] using wordTrace_append hprefix tailTrace_2558579
  have hstable : (prefixWord ++ tailWord_2558579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558579).length < 2 ^ (prefixWord ++ tailWord_2558579).sum := by decide
  have hdescent : baseEnd_2558579 < baseStart_2558579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558593 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 3, 4, 2]
def baseStart_2558593 : Nat := 118140960795 + 2558593 * 2 ^ 59
def prefixEnd_2558593 : Nat := 4983230072969 + 3 ^ 40 * 2558593 * 2
def baseEnd_2558593 : Nat := 1313788008229213226820751

theorem tailTrace_2558593 : CollatzResearch.WordTrace tailWord_2558593 prefixEnd_2558593 1313788008229213226820751 := by
  unfold tailWord_2558593
  simp only [CollatzResearch.WordTrace]
  refine ⟨93319553219662008740320433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62213035479774672493546955 93319553219662008740320433)
  ·
    refine ⟨69989664914746506555240325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93319553219662008740320433 69989664914746506555240325)
    ·
      refine ⟨13123062171514969979107561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69989664914746506555240325 13123062171514969979107561)
      ·
        refine ⟨9842296628636227484330671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13123062171514969979107561 9842296628636227484330671)
        ·
          refine ⟨14763444942954341226496007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9842296628636227484330671 14763444942954341226496007)
          ·
            refine ⟨22145167414431511839744011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14763444942954341226496007 22145167414431511839744011)
            ·
              refine ⟨33217751121647267759616017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22145167414431511839744011 33217751121647267759616017)
              ·
                refine ⟨24913313341235450819712013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33217751121647267759616017 24913313341235450819712013)
                ·
                  refine ⟨9342492502963294057392005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24913313341235450819712013 9342492502963294057392005)
                  ·
                    refine ⟨1751717344305617635761001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9342492502963294057392005 1751717344305617635761001)
                    ·
                      refine ⟨1313788008229213226820751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1751717344305617635761001 1313788008229213226820751)
                      ·
                        rfl

theorem cell23_2558593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_2558593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558593 prefixEnd_2558593 := by exact prefixLift 2558593
  have htrace : WordTrace (prefixWord ++ tailWord_2558593) baseStart_2558593 baseEnd_2558593 := by
    simpa [prefixWord, tailWord_2558593, baseEnd_2558593] using wordTrace_append hprefix tailTrace_2558593
  have hstable : (prefixWord ++ tailWord_2558593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558593).length < 2 ^ (prefixWord ++ tailWord_2558593).sum := by decide
  have hdescent : baseEnd_2558593 < baseStart_2558593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558594 : List Nat := [3, 4, 3, 1, 2, 1, 1, 8]
def baseStart_2558594 : Nat := 118140960795 + 2558594 * 2 ^ 59
def prefixEnd_2558594 : Nat := 4983230072969 + 3 ^ 40 * 2558594 * 2
def baseEnd_2558594 : Nat := 48658834137402508255861

theorem tailTrace_2558594 : CollatzResearch.WordTrace tailWord_2558594 prefixEnd_2558594 48658834137402508255861 := by
  unfold tailWord_2558594
  simp only [CollatzResearch.WordTrace]
  refine ⟨23329897423164596477776709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62213059795105590607404557 23329897423164596477776709)
  ·
    refine ⟨4374355766843361839583133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23329897423164596477776709 4374355766843361839583133)
    ·
      refine ⟨1640383412566260689843675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4374355766843361839583133 1640383412566260689843675)
      ·
        refine ⟨2460575118849391034765513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1640383412566260689843675 2460575118849391034765513)
        ·
          refine ⟨1845431339137043276074135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2460575118849391034765513 1845431339137043276074135)
          ·
            refine ⟨2768147008705564914111203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1845431339137043276074135 2768147008705564914111203)
            ·
              refine ⟨4152220513058347371166805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2768147008705564914111203 4152220513058347371166805)
              ·
                refine ⟨48658834137402508255861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4152220513058347371166805 48658834137402508255861)
                ·
                  rfl

theorem cell23_2558594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 8].length) (baseStart_2558594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558594 prefixEnd_2558594 := by exact prefixLift 2558594
  have htrace : WordTrace (prefixWord ++ tailWord_2558594) baseStart_2558594 baseEnd_2558594 := by
    simpa [prefixWord, tailWord_2558594, baseEnd_2558594] using wordTrace_append hprefix tailTrace_2558594
  have hstable : (prefixWord ++ tailWord_2558594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558594).length < 2 ^ (prefixWord ++ tailWord_2558594).sum := by decide
  have hdescent : baseEnd_2558594 < baseStart_2558594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558609 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 7]
def baseStart_2558609 : Nat := 118140960795 + 2558609 * 2 ^ 59
def prefixEnd_2558609 : Nat := 4983230072969 + 3 ^ 40 * 2558609 * 2
def baseEnd_2558609 : Nat := 1313796223919685164220677

theorem tailTrace_2558609 : CollatzResearch.WordTrace tailWord_2558609 prefixEnd_2558609 1313796223919685164220677 := by
  unfold tailWord_2558609
  simp only [CollatzResearch.WordTrace]
  refine ⟨93320136787604043472902881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62213424525069362315268587 93320136787604043472902881)
  ·
    refine ⟨69990102590703032604677161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93320136787604043472902881 69990102590703032604677161)
    ·
      refine ⟨52492576943027274453507871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69990102590703032604677161 52492576943027274453507871)
      ·
        refine ⟨78738865414540911680261807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52492576943027274453507871 78738865414540911680261807)
        ·
          refine ⟨118108298121811367520392711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78738865414540911680261807 118108298121811367520392711)
          ·
            refine ⟨177162447182717051280589067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118108298121811367520392711 177162447182717051280589067)
            ·
              refine ⟨265743670774075576920883601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177162447182717051280589067 265743670774075576920883601)
              ·
                refine ⟨199307753080556682690662701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 265743670774075576920883601 199307753080556682690662701)
                ·
                  refine ⟨74740407405208756008998513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 199307753080556682690662701 74740407405208756008998513)
                  ·
                    refine ⟨56055305553906567006748885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74740407405208756008998513 56055305553906567006748885)
                    ·
                      refine ⟨1313796223919685164220677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56055305553906567006748885 1313796223919685164220677)
                      ·
                        rfl

theorem cell23_2558609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_2558609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558609 prefixEnd_2558609 := by exact prefixLift 2558609
  have htrace : WordTrace (prefixWord ++ tailWord_2558609) baseStart_2558609 baseEnd_2558609 := by
    simpa [prefixWord, tailWord_2558609, baseEnd_2558609] using wordTrace_append hprefix tailTrace_2558609
  have hstable : (prefixWord ++ tailWord_2558609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558609).length < 2 ^ (prefixWord ++ tailWord_2558609).sum := by decide
  have hdescent : baseEnd_2558609 < baseStart_2558609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558610 : List Nat := [3, 2, 3, 1, 2, 1, 1, 3, 1, 4, 2]
def baseStart_2558610 : Nat := 118140960795 + 2558610 * 2 ^ 59
def prefixEnd_2558610 : Nat := 4983230072969 + 3 ^ 40 * 2558610 * 2
def baseEnd_2558610 : Nat := 1313796737400339660308173

theorem tailTrace_2558610 : CollatzResearch.WordTrace tailWord_2558610 prefixEnd_2558610 1313796737400339660308173 := by
  unfold tailWord_2558610
  simp only [CollatzResearch.WordTrace]
  refine ⟨23330043315150105160922321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62213448840400280429126189 23330043315150105160922321)
  ·
    refine ⟨17497532486362578870691741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23330043315150105160922321 17497532486362578870691741)
    ·
      refine ⟨6561574682385967076509403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17497532486362578870691741 6561574682385967076509403)
      ·
        refine ⟨9842362023578950614764105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6561574682385967076509403 9842362023578950614764105)
        ·
          refine ⟨7381771517684212961073079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9842362023578950614764105 7381771517684212961073079)
          ·
            refine ⟨11072657276526319441609619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7381771517684212961073079 11072657276526319441609619)
            ·
              refine ⟨16608985914789479162414429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11072657276526319441609619 16608985914789479162414429)
              ·
                refine ⟨6228369718046054685905411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16608985914789479162414429 6228369718046054685905411)
                ·
                  refine ⟨9342554577069082028858117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6228369718046054685905411 9342554577069082028858117)
                  ·
                    refine ⟨1751728983200452880410897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9342554577069082028858117 1751728983200452880410897)
                    ·
                      refine ⟨1313796737400339660308173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1751728983200452880410897 1313796737400339660308173)
                      ·
                        rfl

theorem cell23_2558610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_2558610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558610 prefixEnd_2558610 := by exact prefixLift 2558610
  have htrace : WordTrace (prefixWord ++ tailWord_2558610) baseStart_2558610 baseEnd_2558610 := by
    simpa [prefixWord, tailWord_2558610, baseEnd_2558610] using wordTrace_append hprefix tailTrace_2558610
  have hstable : (prefixWord ++ tailWord_2558610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558610).length < 2 ^ (prefixWord ++ tailWord_2558610).sum := by decide
  have hdescent : baseEnd_2558610 < baseStart_2558610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558616 : List Nat := [2, 1, 2, 4, 1, 1, 3, 2, 7]
def baseStart_2558616 : Nat := 118140960795 + 2558616 * 2 ^ 59
def prefixEnd_2558616 : Nat := 4983230072969 + 3 ^ 40 * 2558616 * 2
def baseEnd_2558616 : Nat := 145977757587140737425905

theorem tailTrace_2558616 : CollatzResearch.WordTrace tailWord_2558616 prefixEnd_2558616 145977757587140737425905 := by
  unfold tailWord_2558616
  simp only [CollatzResearch.WordTrace]
  refine ⟨46660196049289341834203851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62213594732385789112271801 46660196049289341834203851)
  ·
    refine ⟨69990294073934012751305777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46660196049289341834203851 69990294073934012751305777)
    ·
      refine ⟨52492720555450509563479333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69990294073934012751305777 52492720555450509563479333)
      ·
        refine ⟨9842385104146970543152375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52492720555450509563479333 9842385104146970543152375)
        ·
          refine ⟨14763577656220455814728563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9842385104146970543152375 14763577656220455814728563)
          ·
            refine ⟨22145366484330683722092845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14763577656220455814728563 22145366484330683722092845)
            ·
              refine ⟨8304512431624006395784817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22145366484330683722092845 8304512431624006395784817)
              ·
                refine ⟨6228384323718004796838613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8304512431624006395784817 6228384323718004796838613)
                ·
                  refine ⟨145977757587140737425905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6228384323718004796838613 145977757587140737425905)
                  ·
                    rfl

theorem cell23_2558616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 7].length) (baseStart_2558616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558616 prefixEnd_2558616 := by exact prefixLift 2558616
  have htrace : WordTrace (prefixWord ++ tailWord_2558616) baseStart_2558616 baseEnd_2558616 := by
    simpa [prefixWord, tailWord_2558616, baseEnd_2558616] using wordTrace_append hprefix tailTrace_2558616
  have hstable : (prefixWord ++ tailWord_2558616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558616).length < 2 ^ (prefixWord ++ tailWord_2558616).sum := by decide
  have hdescent : baseEnd_2558616 < baseStart_2558616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558631 : List Nat := [1, 1, 6, 3, 1, 2, 2, 1, 1, 3, 2]
def baseStart_2558631 : Nat := 118140960795 + 2558631 * 2 ^ 59
def prefixEnd_2558631 : Nat := 4983230072969 + 3 ^ 40 * 2558631 * 2
def baseEnd_2558631 : Nat := 1313807520494084078145577

theorem tailTrace_2558631 : CollatzResearch.WordTrace tailWord_2558631 prefixEnd_2558631 1313807520494084078145577 := by
  unfold tailWord_2558631
  simp only [CollatzResearch.WordTrace]
  refine ⟨93320939193524341230203747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62213959462349560820135831 93320939193524341230203747)
  ·
    refine ⟨139981408790286511845305621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93320939193524341230203747 139981408790286511845305621)
    ·
      refine ⟨6561628537044680242748701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 139981408790286511845305621 6561628537044680242748701)
      ·
        refine ⟨2460610701391755091030763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6561628537044680242748701 2460610701391755091030763)
        ·
          refine ⟨3690916052087632636546145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2460610701391755091030763 3690916052087632636546145)
          ·
            refine ⟨2768187039065724477409609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3690916052087632636546145 2768187039065724477409609)
            ·
              refine ⟨2076140279299293358057207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2768187039065724477409609 2076140279299293358057207)
              ·
                refine ⟨3114210418948940037085811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2076140279299293358057207 3114210418948940037085811)
                ·
                  refine ⟨4671315628423410055628717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3114210418948940037085811 4671315628423410055628717)
                  ·
                    refine ⟨1751743360658778770860769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4671315628423410055628717 1751743360658778770860769)
                    ·
                      refine ⟨1313807520494084078145577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1751743360658778770860769 1313807520494084078145577)
                      ·
                        rfl

theorem cell23_2558631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_2558631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558631 prefixEnd_2558631 := by exact prefixLift 2558631
  have htrace : WordTrace (prefixWord ++ tailWord_2558631) baseStart_2558631 baseEnd_2558631 := by
    simpa [prefixWord, tailWord_2558631, baseEnd_2558631] using wordTrace_append hprefix tailTrace_2558631
  have hstable : (prefixWord ++ tailWord_2558631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558631).length < 2 ^ (prefixWord ++ tailWord_2558631).sum := by decide
  have hdescent : baseEnd_2558631 < baseStart_2558631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558703 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 4, 2, 3]
def baseStart_2558703 : Nat := 118140960795 + 2558703 * 2 ^ 59
def prefixEnd_2558703 : Nat := 4983230072969 + 3 ^ 40 * 2558703 * 2
def baseEnd_2558703 : Nat := 1313844491101207796445245

theorem tailTrace_2558703 : CollatzResearch.WordTrace tailWord_2558703 prefixEnd_2558703 1313844491101207796445245 := by
  unfold tailWord_2558703
  simp only [CollatzResearch.WordTrace]
  refine ⟨93323565249263497526824763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62215710166175665017883175 93323565249263497526824763)
  ·
    refine ⟨139985347873895246290237145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93323565249263497526824763 139985347873895246290237145)
    ·
      refine ⟨104989010905421434717677859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139985347873895246290237145 104989010905421434717677859)
      ·
        refine ⟨157483516358132152076516789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104989010905421434717677859 157483516358132152076516789)
        ·
          refine ⟨14764079658574889257173449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 157483516358132152076516789 14764079658574889257173449)
          ·
            refine ⟨11073059743931166942880087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14764079658574889257173449 11073059743931166942880087)
            ·
              refine ⟨16609589615896750414320131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11073059743931166942880087 16609589615896750414320131)
              ·
                refine ⟨24914384423845125621480197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16609589615896750414320131 24914384423845125621480197)
                ·
                  refine ⟨4671447079470961054027537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24914384423845125621480197 4671447079470961054027537)
                  ·
                    refine ⟨3503585309603220790520653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4671447079470961054027537 3503585309603220790520653)
                    ·
                      refine ⟨1313844491101207796445245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3503585309603220790520653 1313844491101207796445245)
                      ·
                        rfl

theorem cell23_2558703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2, 3].length) (baseStart_2558703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558703 prefixEnd_2558703 := by exact prefixLift 2558703
  have htrace : WordTrace (prefixWord ++ tailWord_2558703) baseStart_2558703 baseEnd_2558703 := by
    simpa [prefixWord, tailWord_2558703, baseEnd_2558703] using wordTrace_append hprefix tailTrace_2558703
  have hstable : (prefixWord ++ tailWord_2558703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558703).length < 2 ^ (prefixWord ++ tailWord_2558703).sum := by decide
  have hdescent : baseEnd_2558703 < baseStart_2558703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558783 : List Nat := [1, 1, 2, 2, 5, 1, 1, 3, 1, 6]
def baseStart_2558783 : Nat := 118140960795 + 2558783 * 2 ^ 59
def prefixEnd_2558783 : Nat := 4983230072969 + 3 ^ 40 * 2558783 * 2
def baseEnd_2558783 : Nat := 437961856517855827814959

theorem tailTrace_2558783 : CollatzResearch.WordTrace tailWord_2558783 prefixEnd_2558783 437961856517855827814959 := by
  unfold tailWord_2558783
  simp only [CollatzResearch.WordTrace]
  refine ⟨93326483088973671189737003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62217655392649114126491335 93326483088973671189737003)
  ·
    refine ⟨139989724633460506784605505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93326483088973671189737003 139989724633460506784605505)
    ·
      refine ⟨104992293475095380088454129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139989724633460506784605505 104992293475095380088454129)
      ·
        refine ⟨78744220106321535066340597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104992293475095380088454129 78744220106321535066340597)
        ·
          refine ⟨7382270634967643912469431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78744220106321535066340597 7382270634967643912469431)
          ·
            refine ⟨11073405952451465868704147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7382270634967643912469431 11073405952451465868704147)
            ·
              refine ⟨16610108928677198803056221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11073405952451465868704147 16610108928677198803056221)
              ·
                refine ⟨6228790848253949551146083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16610108928677198803056221 6228790848253949551146083)
                ·
                  refine ⟨9343186272380924326719125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6228790848253949551146083 9343186272380924326719125)
                  ·
                    refine ⟨437961856517855827814959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9343186272380924326719125 437961856517855827814959)
                    ·
                      rfl

theorem cell23_2558783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 6].length) (baseStart_2558783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558783 prefixEnd_2558783 := by exact prefixLift 2558783
  have htrace : WordTrace (prefixWord ++ tailWord_2558783) baseStart_2558783 baseEnd_2558783 := by
    simpa [prefixWord, tailWord_2558783, baseEnd_2558783] using wordTrace_append hprefix tailTrace_2558783
  have hstable : (prefixWord ++ tailWord_2558783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558783).length < 2 ^ (prefixWord ++ tailWord_2558783).sum := by decide
  have hdescent : baseEnd_2558783 < baseStart_2558783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558804 : List Nat := [2, 4, 1, 1, 4, 2, 2, 1, 1, 5]
def baseStart_2558804 : Nat := 118140960795 + 2558804 * 2 ^ 59
def prefixEnd_2558804 : Nat := 4983230072969 + 3 ^ 40 * 2558804 * 2
def baseEnd_2558804 : Nat := 437965450882437300427427

theorem tailTrace_2558804 : CollatzResearch.WordTrace tailWord_2558804 prefixEnd_2558804 437965450882437300427427 := by
  unfold tailWord_2558804
  simp only [CollatzResearch.WordTrace]
  refine ⟨46663624510948795888125733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62218166014598394517500977 46663624510948795888125733)
  ·
    refine ⟨8749429595802899229023575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46663624510948795888125733 8749429595802899229023575)
    ·
      refine ⟨13124144393704348843535363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8749429595802899229023575 13124144393704348843535363)
      ·
        refine ⟨19686216590556523265303045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13124144393704348843535363 19686216590556523265303045)
        ·
          refine ⟨3691165610729348112244321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19686216590556523265303045 3691165610729348112244321)
          ·
            refine ⟨2768374208047011084183241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3691165610729348112244321 2768374208047011084183241)
            ·
              refine ⟨2076280656035258313137431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2768374208047011084183241 2076280656035258313137431)
              ·
                refine ⟨3114420984052887469706147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2076280656035258313137431 3114420984052887469706147)
                ·
                  refine ⟨4671631476079331204559221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3114420984052887469706147 4671631476079331204559221)
                  ·
                    refine ⟨437965450882437300427427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4671631476079331204559221 437965450882437300427427)
                    ·
                      rfl

theorem cell23_2558804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_2558804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558804 prefixEnd_2558804 := by exact prefixLift 2558804
  have htrace : WordTrace (prefixWord ++ tailWord_2558804) baseStart_2558804 baseEnd_2558804 := by
    simpa [prefixWord, tailWord_2558804, baseEnd_2558804] using wordTrace_append hprefix tailTrace_2558804
  have hstable : (prefixWord ++ tailWord_2558804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558804).length < 2 ^ (prefixWord ++ tailWord_2558804).sum := by decide
  have hdescent : baseEnd_2558804 < baseStart_2558804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558807 : List Nat := [1, 1, 3, 2, 4, 1, 4, 1, 1, 1, 4]
def baseStart_2558807 : Nat := 118140960795 + 2558807 * 2 ^ 59
def prefixEnd_2558807 : Nat := 4983230072969 + 3 ^ 40 * 2558807 * 2
def baseEnd_2558807 : Nat := 1313897893089275389544767

theorem tailTrace_2558807 : CollatzResearch.WordTrace tailWord_2558807 prefixEnd_2558807 1313897893089275389544767 := by
  unfold tailWord_2558807
  simp only [CollatzResearch.WordTrace]
  refine ⟨93327358440886723288610675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62218238960591148859073783 93327358440886723288610675)
  ·
    refine ⟨139991037661330084932916013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93327358440886723288610675 139991037661330084932916013)
    ·
      refine ⟨52496639122998781849843505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139991037661330084932916013 52496639122998781849843505)
      ·
        refine ⟨39372479342249086387382629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52496639122998781849843505 39372479342249086387382629)
        ·
          refine ⟨7382339876671703697634243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39372479342249086387382629 7382339876671703697634243)
          ·
            refine ⟨11073509815007555546451365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7382339876671703697634243 11073509815007555546451365)
            ·
              refine ⟨2076283090313916664959631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11073509815007555546451365 2076283090313916664959631)
              ·
                refine ⟨3114424635470874997439447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2076283090313916664959631 3114424635470874997439447)
                ·
                  refine ⟨4671636953206312496159171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3114424635470874997439447 4671636953206312496159171)
                  ·
                    refine ⟨7007455429809468744238757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4671636953206312496159171 7007455429809468744238757)
                    ·
                      refine ⟨1313897893089275389544767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7007455429809468744238757 1313897893089275389544767)
                      ·
                        rfl

theorem cell23_2558807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 1, 1, 4].length) (baseStart_2558807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558807 prefixEnd_2558807 := by exact prefixLift 2558807
  have htrace : WordTrace (prefixWord ++ tailWord_2558807) baseStart_2558807 baseEnd_2558807 := by
    simpa [prefixWord, tailWord_2558807, baseEnd_2558807] using wordTrace_append hprefix tailTrace_2558807
  have hstable : (prefixWord ++ tailWord_2558807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558807).length < 2 ^ (prefixWord ++ tailWord_2558807).sum := by decide
  have hdescent : baseEnd_2558807 < baseStart_2558807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558824 : List Nat := [2, 1, 4, 2, 1, 3, 2, 1, 3, 2, 2]
def baseStart_2558824 : Nat := 118140960795 + 2558824 * 2 ^ 59
def prefixEnd_2558824 : Nat := 4983230072969 + 3 ^ 40 * 2558824 * 2
def baseEnd_2558824 : Nat := 1313906622260401823032189

theorem tailTrace_2558824 : CollatzResearch.WordTrace tailWord_2558824 prefixEnd_2558824 1313906622260401823032189 := by
  unfold tailWord_2558824
  simp only [CollatzResearch.WordTrace]
  refine ⟨46663989240912567595989763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62218652321216756794653017 46663989240912567595989763)
  ·
    refine ⟨69995983861368851393984645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46663989240912567595989763 69995983861368851393984645)
    ·
      refine ⟨13124246974006659636372121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69995983861368851393984645 13124246974006659636372121)
      ·
        refine ⟨9843185230504994727279091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13124246974006659636372121 9843185230504994727279091)
        ·
          refine ⟨14764777845757492090918637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9843185230504994727279091 14764777845757492090918637)
          ·
            refine ⟨5536791692159059534094489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14764777845757492090918637 5536791692159059534094489)
            ·
              refine ⟨4152593769119294650570867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5536791692159059534094489 4152593769119294650570867)
              ·
                refine ⟨6228890653678941975856301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4152593769119294650570867 6228890653678941975856301)
                ·
                  refine ⟨2335833995129603240946113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6228890653678941975856301 2335833995129603240946113)
                  ·
                    refine ⟨1751875496347202430709585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2335833995129603240946113 1751875496347202430709585)
                    ·
                      refine ⟨1313906622260401823032189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1751875496347202430709585 1313906622260401823032189)
                      ·
                        rfl

theorem cell23_2558824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_2558824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558824 prefixEnd_2558824 := by exact prefixLift 2558824
  have htrace : WordTrace (prefixWord ++ tailWord_2558824) baseStart_2558824 baseEnd_2558824 := by
    simpa [prefixWord, tailWord_2558824, baseEnd_2558824] using wordTrace_append hprefix tailTrace_2558824
  have hstable : (prefixWord ++ tailWord_2558824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558824).length < 2 ^ (prefixWord ++ tailWord_2558824).sum := by decide
  have hdescent : baseEnd_2558824 < baseStart_2558824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558837 : List Nat := [1, 3, 4, 1, 1, 4, 1, 1, 1, 2, 4]
def baseStart_2558837 : Nat := 118140960795 + 2558837 * 2 ^ 59
def prefixEnd_2558837 : Nat := 4983230072969 + 3 ^ 40 * 2558837 * 2
def baseEnd_2558837 : Nat := 1313913297508910272169629

theorem tailTrace_2558837 : CollatzResearch.WordTrace tailWord_2558837 prefixEnd_2558837 1313913297508910272169629 := by
  unfold tailWord_2558837
  simp only [CollatzResearch.WordTrace]
  refine ⟨93328452630778038412202765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62218968420518692274801843 93328452630778038412202765)
  ·
    refine ⟨34998169736541764404576037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93328452630778038412202765 34998169736541764404576037)
    ·
      refine ⟨6562156825601580825858007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34998169736541764404576037 6562156825601580825858007)
      ·
        refine ⟨9843235238402371238787011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6562156825601580825858007 9843235238402371238787011)
        ·
          refine ⟨14764852857603556858180517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9843235238402371238787011 14764852857603556858180517)
          ·
            refine ⟨2768409910800666910908847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14764852857603556858180517 2768409910800666910908847)
            ·
              refine ⟨4152614866201000366363271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2768409910800666910908847 4152614866201000366363271)
              ·
                refine ⟨6228922299301500549544907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4152614866201000366363271 6228922299301500549544907)
                ·
                  refine ⟨9343383448952250824317361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6228922299301500549544907 9343383448952250824317361)
                  ·
                    refine ⟨7007537586714188118238021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9343383448952250824317361 7007537586714188118238021)
                    ·
                      refine ⟨1313913297508910272169629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7007537586714188118238021 1313913297508910272169629)
                      ·
                        rfl

theorem cell23_2558837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_2558837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558837 prefixEnd_2558837 := by exact prefixLift 2558837
  have htrace : WordTrace (prefixWord ++ tailWord_2558837) baseStart_2558837 baseEnd_2558837 := by
    simpa [prefixWord, tailWord_2558837, baseEnd_2558837] using wordTrace_append hprefix tailTrace_2558837
  have hstable : (prefixWord ++ tailWord_2558837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558837).length < 2 ^ (prefixWord ++ tailWord_2558837).sum := by decide
  have hdescent : baseEnd_2558837 < baseStart_2558837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558853 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 2, 2, 5]
def baseStart_2558853 : Nat := 118140960795 + 2558853 * 2 ^ 59
def prefixEnd_2558853 : Nat := 4983230072969 + 3 ^ 40 * 2558853 * 2
def baseEnd_2558853 : Nat := 1313921513199382209569555

theorem tailTrace_2558853 : CollatzResearch.WordTrace tailWord_2558853 prefixEnd_2558853 1313921513199382209569555 := by
  unfold tailWord_2558853
  simp only [CollatzResearch.WordTrace]
  refine ⟨93329036198720073144785213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62219357465813382096523475 93329036198720073144785213)
  ·
    refine ⟨34998388574520027429294455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93329036198720073144785213 34998388574520027429294455)
    ·
      refine ⟨52497582861780041143941683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34998388574520027429294455 52497582861780041143941683)
      ·
        refine ⟨78746374292670061715912525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52497582861780041143941683 78746374292670061715912525)
        ·
          refine ⟨29529890359751273143467197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78746374292670061715912525 29529890359751273143467197)
          ·
            refine ⟨11073708884906727428800199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29529890359751273143467197 11073708884906727428800199)
            ·
              refine ⟨16610563327360091143200299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11073708884906727428800199 16610563327360091143200299)
              ·
                refine ⟨24915844991040136714800449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16610563327360091143200299 24915844991040136714800449)
                ·
                  refine ⟨18686883743280102536100337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24915844991040136714800449 18686883743280102536100337)
                  ·
                    refine ⟨14015162807460076902075253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18686883743280102536100337 14015162807460076902075253)
                    ·
                      refine ⟨1313921513199382209569555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14015162807460076902075253 1313921513199382209569555)
                      ·
                        rfl

theorem cell23_2558853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_2558853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558853 prefixEnd_2558853 := by exact prefixLift 2558853
  have htrace : WordTrace (prefixWord ++ tailWord_2558853) baseStart_2558853 baseEnd_2558853 := by
    simpa [prefixWord, tailWord_2558853, baseEnd_2558853] using wordTrace_append hprefix tailTrace_2558853
  have hstable : (prefixWord ++ tailWord_2558853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558853).length < 2 ^ (prefixWord ++ tailWord_2558853).sum := by decide
  have hdescent : baseEnd_2558853 < baseStart_2558853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558858 : List Nat := [3, 1, 2, 4, 1, 3, 1, 3, 1, 2, 2]
def baseStart_2558858 : Nat := 118140960795 + 2558858 * 2 ^ 59
def prefixEnd_2558858 : Nat := 4983230072969 + 3 ^ 40 * 2558858 * 2
def baseEnd_2558858 : Nat := 1313924080602654690007033

theorem tailTrace_2558858 : CollatzResearch.WordTrace tailWord_2558858 prefixEnd_2558858 1313924080602654690007033 := by
  unfold tailWord_2558858
  simp only [CollatzResearch.WordTrace]
  refine ⟨23332304640925489749679307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62219479042467972665811485 23332304640925489749679307)
  ·
    refine ⟨34998456961388234624518961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23332304640925489749679307 34998456961388234624518961)
    ·
      refine ⟨26248842721041175968389221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34998456961388234624518961 26248842721041175968389221)
      ·
        refine ⟨4921658010195220494072979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26248842721041175968389221 4921658010195220494072979)
        ·
          refine ⟨7382487015292830741109469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4921658010195220494072979 7382487015292830741109469)
          ·
            refine ⟨2768432630734811527916051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7382487015292830741109469 2768432630734811527916051)
            ·
              refine ⟨4152648946102217291874077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2768432630734811527916051 4152648946102217291874077)
              ·
                refine ⟨1557243354788331484452779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4152648946102217291874077 1557243354788331484452779)
                ·
                  refine ⟨2335865032182497226679169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1557243354788331484452779 2335865032182497226679169)
                  ·
                    refine ⟨1751898774136872920009377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2335865032182497226679169 1751898774136872920009377)
                    ·
                      refine ⟨1313924080602654690007033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1751898774136872920009377 1313924080602654690007033)
                      ·
                        rfl

theorem cell23_2558858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_2558858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558858 prefixEnd_2558858 := by exact prefixLift 2558858
  have htrace : WordTrace (prefixWord ++ tailWord_2558858) baseStart_2558858 baseEnd_2558858 := by
    simpa [prefixWord, tailWord_2558858, baseEnd_2558858] using wordTrace_append hprefix tailTrace_2558858
  have hstable : (prefixWord ++ tailWord_2558858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558858).length < 2 ^ (prefixWord ++ tailWord_2558858).sum := by decide
  have hdescent : baseEnd_2558858 < baseStart_2558858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558903 : List Nat := [1, 1, 3, 1, 3, 1, 2, 4, 7]
def baseStart_2558903 : Nat := 118140960795 + 2558903 * 2 ^ 59
def prefixEnd_2558903 : Nat := 4983230072969 + 3 ^ 40 * 2558903 * 2
def baseEnd_2558903 : Nat := 145994131914678557104925

theorem tailTrace_2558903 : CollatzResearch.WordTrace tailWord_2558903 prefixEnd_2558903 145994131914678557104925 := by
  unfold tailWord_2558903
  simp only [CollatzResearch.WordTrace]
  refine ⟨93330859848538931684105363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62220573232359287789403575 93330859848538931684105363)
  ·
    refine ⟨139996289772808397526158045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93330859848538931684105363 139996289772808397526158045)
    ·
      refine ⟨52498608664803149072309267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139996289772808397526158045 52498608664803149072309267)
      ·
        refine ⟨78747912997204723608463901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52498608664803149072309267 78747912997204723608463901)
        ·
          refine ⟨29530467373951771353173963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78747912997204723608463901 29530467373951771353173963)
          ·
            refine ⟨44295701060927657029760945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29530467373951771353173963 44295701060927657029760945)
            ·
              refine ⟨33221775795695742772320709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44295701060927657029760945 33221775795695742772320709)
              ·
                refine ⟨6229082961692951769810133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33221775795695742772320709 6229082961692951769810133)
                ·
                  refine ⟨145994131914678557104925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6229082961692951769810133 145994131914678557104925)
                  ·
                    rfl

theorem cell23_2558903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 7].length) (baseStart_2558903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558903 prefixEnd_2558903 := by exact prefixLift 2558903
  have htrace : WordTrace (prefixWord ++ tailWord_2558903) baseStart_2558903 baseEnd_2558903 := by
    simpa [prefixWord, tailWord_2558903, baseEnd_2558903] using wordTrace_append hprefix tailTrace_2558903
  have hstable : (prefixWord ++ tailWord_2558903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558903).length < 2 ^ (prefixWord ++ tailWord_2558903).sum := by decide
  have hdescent : baseEnd_2558903 < baseStart_2558903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558925 : List Nat := [1, 6, 3, 1, 1, 1, 2, 2, 2, 1, 3]
def baseStart_2558925 : Nat := 118140960795 + 2558925 * 2 ^ 59
def prefixEnd_2558925 : Nat := 4983230072969 + 3 ^ 40 * 2558925 * 2
def baseEnd_2558925 : Nat := 1313958483806505927869225

theorem tailTrace_2558925 : CollatzResearch.WordTrace tailWord_2558925 prefixEnd_2558925 1313958483806505927869225 := by
  unfold tailWord_2558925
  simp only [CollatzResearch.WordTrace]
  refine ⟨93331662254459229441406229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62221108169639486294270819 93331662254459229441406229)
  ·
    refine ⟨4374921668177776380065917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93331662254459229441406229 4374921668177776380065917)
    ·
      refine ⟨1640595625566666142524719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4374921668177776380065917 1640595625566666142524719)
      ·
        refine ⟨2460893438349999213787079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1640595625566666142524719 2460893438349999213787079)
        ·
          refine ⟨3691340157524998820680619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2460893438349999213787079 3691340157524998820680619)
          ·
            refine ⟨5537010236287498231020929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3691340157524998820680619 5537010236287498231020929)
            ·
              refine ⟨4152757677215623673265697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5537010236287498231020929 4152757677215623673265697)
              ·
                refine ⟨3114568257911717754949273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4152757677215623673265697 3114568257911717754949273)
                ·
                  refine ⟨2335926193433788316211955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3114568257911717754949273 2335926193433788316211955)
                  ·
                    refine ⟨3503889290150682474317933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2335926193433788316211955 3503889290150682474317933)
                    ·
                      refine ⟨1313958483806505927869225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3503889290150682474317933 1313958483806505927869225)
                      ·
                        rfl

theorem cell23_2558925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_2558925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558925 prefixEnd_2558925 := by exact prefixLift 2558925
  have htrace : WordTrace (prefixWord ++ tailWord_2558925) baseStart_2558925 baseEnd_2558925 := by
    simpa [prefixWord, tailWord_2558925, baseEnd_2558925] using wordTrace_append hprefix tailTrace_2558925
  have hstable : (prefixWord ++ tailWord_2558925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558925).length < 2 ^ (prefixWord ++ tailWord_2558925).sum := by decide
  have hdescent : baseEnd_2558925 < baseStart_2558925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558937 : List Nat := [1, 2, 1, 2, 5, 2, 1, 4, 5]
def baseStart_2558937 : Nat := 118140960795 + 2558937 * 2 ^ 59
def prefixEnd_2558937 : Nat := 4983230072969 + 3 ^ 40 * 2558937 * 2
def baseEnd_2558937 : Nat := 145996071730484431213241

theorem tailTrace_2558937 : CollatzResearch.WordTrace tailWord_2558937 prefixEnd_2558937 145996071730484431213241 := by
  unfold tailWord_2558937
  simp only [CollatzResearch.WordTrace]
  refine ⟨93332099930415755490843065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62221399953610503660562043 93332099930415755490843065)
  ·
    refine ⟨69999074947811816618132299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93332099930415755490843065 69999074947811816618132299)
    ·
      refine ⟨104998612421717724927198449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69999074947811816618132299 104998612421717724927198449)
      ·
        refine ⟨78748959316288293695398837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104998612421717724927198449 78748959316288293695398837)
        ·
          refine ⟨7382714935902027533943641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78748959316288293695398837 7382714935902027533943641)
          ·
            refine ⟨5537036201926520650457731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7382714935902027533943641 5537036201926520650457731)
            ·
              refine ⟨8305554302889780975686597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5537036201926520650457731 8305554302889780975686597)
              ·
                refine ⟨1557291431791833932941237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8305554302889780975686597 1557291431791833932941237)
                ·
                  refine ⟨145996071730484431213241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1557291431791833932941237 145996071730484431213241)
                  ·
                    rfl

theorem cell23_2558937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4, 5].length) (baseStart_2558937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558937 prefixEnd_2558937 := by exact prefixLift 2558937
  have htrace : WordTrace (prefixWord ++ tailWord_2558937) baseStart_2558937 baseEnd_2558937 := by
    simpa [prefixWord, tailWord_2558937, baseEnd_2558937] using wordTrace_append hprefix tailTrace_2558937
  have hstable : (prefixWord ++ tailWord_2558937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558937).length < 2 ^ (prefixWord ++ tailWord_2558937).sum := by decide
  have hdescent : baseEnd_2558937 < baseStart_2558937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558987 : List Nat := [1, 1, 1, 1, 6, 2, 1, 2, 2, 4, 2]
def baseStart_2558987 : Nat := 118140960795 + 2558987 * 2 ^ 59
def prefixEnd_2558987 : Nat := 4983230072969 + 3 ^ 40 * 2558987 * 2
def baseEnd_2558987 : Nat := 1313990319607084685293939

theorem tailTrace_2558987 : CollatzResearch.WordTrace tailWord_2558987 prefixEnd_2558987 1313990319607084685293939 := by
  unfold tailWord_2558987
  simp only [CollatzResearch.WordTrace]
  refine ⟨93333923580234614030163215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62222615720156409353442143 93333923580234614030163215)
  ·
    refine ⟨140000885370351921045244823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93333923580234614030163215 140000885370351921045244823)
    ·
      refine ⟨210001328055527881567867235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140000885370351921045244823 210001328055527881567867235)
      ·
        refine ⟨315001992083291822351800853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210001328055527881567867235 315001992083291822351800853)
        ·
          refine ⟨14765718378904304172740665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 315001992083291822351800853 14765718378904304172740665)
          ·
            refine ⟨11074288784178228129555499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14765718378904304172740665 11074288784178228129555499)
            ·
              refine ⟨16611433176267342194333249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11074288784178228129555499 16611433176267342194333249)
              ·
                refine ⟨12458574882200506645749937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16611433176267342194333249 12458574882200506645749937)
                ·
                  refine ⟨9343931161650379984312453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12458574882200506645749937 9343931161650379984312453)
                  ·
                    refine ⟨1751987092809446247058585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9343931161650379984312453 1751987092809446247058585)
                    ·
                      refine ⟨1313990319607084685293939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1751987092809446247058585 1313990319607084685293939)
                      ·
                        rfl

theorem cell23_2558987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 4, 2].length) (baseStart_2558987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558987 prefixEnd_2558987 := by exact prefixLift 2558987
  have htrace : WordTrace (prefixWord ++ tailWord_2558987) baseStart_2558987 baseEnd_2558987 := by
    simpa [prefixWord, tailWord_2558987, baseEnd_2558987] using wordTrace_append hprefix tailTrace_2558987
  have hstable : (prefixWord ++ tailWord_2558987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558987).length < 2 ^ (prefixWord ++ tailWord_2558987).sum := by decide
  have hdescent : baseEnd_2558987 < baseStart_2558987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2558997 : List Nat := [1, 3, 2, 1, 4, 1, 1, 3, 3, 4]
def baseStart_2558997 : Nat := 118140960795 + 2558997 * 2 ^ 59
def prefixEnd_2558997 : Nat := 4983230072969 + 3 ^ 40 * 2558997 * 2
def baseEnd_2558997 : Nat := 437998484804543215389631

theorem tailTrace_2558997 : CollatzResearch.WordTrace tailWord_2558997 prefixEnd_2558997 437998484804543215389631 := by
  unfold tailWord_2558997
  simp only [CollatzResearch.WordTrace]
  refine ⟨93334288310198385738027245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62222858873465590492018163 93334288310198385738027245)
  ·
    refine ⟨35000358116324394651760217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93334288310198385738027245 35000358116324394651760217)
    ·
      refine ⟨26250268587243295988820163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35000358116324394651760217 26250268587243295988820163)
      ·
        refine ⟨39375402880864943983230245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26250268587243295988820163 39375402880864943983230245)
        ·
          refine ⟨7382888040162176996855671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39375402880864943983230245 7382888040162176996855671)
          ·
            refine ⟨11074332060243265495283507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7382888040162176996855671 11074332060243265495283507)
            ·
              refine ⟨16611498090364898242925261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11074332060243265495283507 16611498090364898242925261)
              ·
                refine ⟨6229311783886836841096973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16611498090364898242925261 6229311783886836841096973)
                ·
                  refine ⟨2335991918957563815411365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6229311783886836841096973 2335991918957563815411365)
                  ·
                    refine ⟨437998484804543215389631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2335991918957563815411365 437998484804543215389631)
                    ·
                      rfl

theorem cell23_2558997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_2558997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2558997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2558997 prefixEnd_2558997 := by exact prefixLift 2558997
  have htrace : WordTrace (prefixWord ++ tailWord_2558997) baseStart_2558997 baseEnd_2558997 := by
    simpa [prefixWord, tailWord_2558997, baseEnd_2558997] using wordTrace_append hprefix tailTrace_2558997
  have hstable : (prefixWord ++ tailWord_2558997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2558997).length < 2 ^ (prefixWord ++ tailWord_2558997).sum := by decide
  have hdescent : baseEnd_2558997 < baseStart_2558997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2558997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559003 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 9]
def baseStart_2559003 : Nat := 118140960795 + 2559003 * 2 ^ 59
def prefixEnd_2559003 : Nat := 4983230072969 + 3 ^ 40 * 2559003 * 2
def baseEnd_2559003 : Nat := 1313998535297556622693865

theorem tailTrace_2559003 : CollatzResearch.WordTrace tailWord_2559003 prefixEnd_2559003 1313998535297556622693865 := by
  unfold tailWord_2559003
  simp only [CollatzResearch.WordTrace]
  refine ⟨93334507148176648762745663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62223004765451099175163775 93334507148176648762745663)
  ·
    refine ⟨140001760722264973144118495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93334507148176648762745663 140001760722264973144118495)
    ·
      refine ⟨210002641083397459716177743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140001760722264973144118495 210002641083397459716177743)
      ·
        refine ⟨315003961625096189574266615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210002641083397459716177743 315003961625096189574266615)
        ·
          refine ⟨472505942437644284361399923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315003961625096189574266615 472505942437644284361399923)
          ·
            refine ⟨708758913656466426542099885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472505942437644284361399923 708758913656466426542099885)
            ·
              refine ⟨265784592621174909953287457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 708758913656466426542099885 265784592621174909953287457)
              ·
                refine ⟨199338444465881182464965593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 265784592621174909953287457 199338444465881182464965593)
                ·
                  refine ⟨149503833349410886848724195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199338444465881182464965593 149503833349410886848724195)
                  ·
                    refine ⟨224255750024116330273086293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 149503833349410886848724195 224255750024116330273086293)
                    ·
                      refine ⟨1313998535297556622693865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 224255750024116330273086293 1313998535297556622693865)
                      ·
                        rfl

theorem cell23_2559003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 9].length) (baseStart_2559003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559003 prefixEnd_2559003 := by exact prefixLift 2559003
  have htrace : WordTrace (prefixWord ++ tailWord_2559003) baseStart_2559003 baseEnd_2559003 := by
    simpa [prefixWord, tailWord_2559003, baseEnd_2559003] using wordTrace_append hprefix tailTrace_2559003
  have hstable : (prefixWord ++ tailWord_2559003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559003).length < 2 ^ (prefixWord ++ tailWord_2559003).sum := by decide
  have hdescent : baseEnd_2559003 < baseStart_2559003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559020 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 3]
def baseStart_2559020 : Nat := 118140960795 + 2559020 * 2 ^ 59
def prefixEnd_2559020 : Nat := 4983230072969 + 3 ^ 40 * 2559020 * 2
def baseEnd_2559020 : Nat := 1314007264468683056181287

theorem tailTrace_2559020 : CollatzResearch.WordTrace tailWord_2559020 prefixEnd_2559020 1314007264468683056181287 := by
  unfold tailWord_2559020
  simp only [CollatzResearch.WordTrace]
  refine ⟨46667563594557530333057257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62223418126076707110743009 46667563594557530333057257)
  ·
    refine ⟨35000672695918147749792943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46667563594557530333057257 35000672695918147749792943)
    ·
      refine ⟨52501009043877221624689415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35000672695918147749792943 52501009043877221624689415)
      ·
        refine ⟨78751513565815832437034123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52501009043877221624689415 78751513565815832437034123)
        ·
          refine ⟨118127270348723748655551185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78751513565815832437034123 118127270348723748655551185)
          ·
            refine ⟨88595452761542811491663389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118127270348723748655551185 88595452761542811491663389)
            ·
              refine ⟨33223294785578554309373771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88595452761542811491663389 33223294785578554309373771)
              ·
                refine ⟨49834942178367831464060657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33223294785578554309373771 49834942178367831464060657)
                ·
                  refine ⟨37376206633775873598045493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49834942178367831464060657 37376206633775873598045493)
                  ·
                    refine ⟨3504019371916488149816765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37376206633775873598045493 3504019371916488149816765)
                    ·
                      refine ⟨1314007264468683056181287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3504019371916488149816765 1314007264468683056181287)
                      ·
                        rfl

theorem cell23_2559020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 3].length) (baseStart_2559020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559020 prefixEnd_2559020 := by exact prefixLift 2559020
  have htrace : WordTrace (prefixWord ++ tailWord_2559020) baseStart_2559020 baseEnd_2559020 := by
    simpa [prefixWord, tailWord_2559020, baseEnd_2559020] using wordTrace_append hprefix tailTrace_2559020
  have hstable : (prefixWord ++ tailWord_2559020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559020).length < 2 ^ (prefixWord ++ tailWord_2559020).sum := by decide
  have hdescent : baseEnd_2559020 < baseStart_2559020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559074 : List Nat := [3, 3, 2, 2, 1, 2, 1, 1, 3, 5]
def baseStart_2559074 : Nat := 118140960795 + 2559074 * 2 ^ 59
def prefixEnd_2559074 : Nat := 4983230072969 + 3 ^ 40 * 2559074 * 2
def baseEnd_2559074 : Nat := 438011664141341948302013

theorem tailTrace_2559074 : CollatzResearch.WordTrace tailWord_2559074 prefixEnd_2559074 438011664141341948302013 := by
  unfold tailWord_2559074
  simp only [CollatzResearch.WordTrace]
  refine ⟨23334274182729856972145069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62224731153946285259053517 23334274182729856972145069)
  ·
    refine ⟨8750352818523696364554401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23334274182729856972145069 8750352818523696364554401)
    ·
      refine ⟨6562764613892772273415801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8750352818523696364554401 6562764613892772273415801)
      ·
        refine ⟨4922073460419579205061851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6562764613892772273415801 4922073460419579205061851)
        ·
          refine ⟨7383110190629368807592777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4922073460419579205061851 7383110190629368807592777)
          ·
            refine ⟨5537332642972026605694583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7383110190629368807592777 5537332642972026605694583)
            ·
              refine ⟨8305998964458039908541875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5537332642972026605694583 8305998964458039908541875)
              ·
                refine ⟨12458998446687059862812813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8305998964458039908541875 12458998446687059862812813)
                ·
                  refine ⟨4672124417507647448554805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12458998446687059862812813 4672124417507647448554805)
                  ·
                    refine ⟨438011664141341948302013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4672124417507647448554805 438011664141341948302013)
                    ·
                      rfl

theorem cell23_2559074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_2559074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559074 prefixEnd_2559074 := by exact prefixLift 2559074
  have htrace : WordTrace (prefixWord ++ tailWord_2559074) baseStart_2559074 baseEnd_2559074 := by
    simpa [prefixWord, tailWord_2559074, baseEnd_2559074] using wordTrace_append hprefix tailTrace_2559074
  have hstable : (prefixWord ++ tailWord_2559074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559074).length < 2 ^ (prefixWord ++ tailWord_2559074).sum := by decide
  have hdescent : baseEnd_2559074 < baseStart_2559074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559077 : List Nat := [1, 3, 1, 3, 2, 1, 3, 1, 3, 1, 4]
def baseStart_2559077 : Nat := 118140960795 + 2559077 * 2 ^ 59
def prefixEnd_2559077 : Nat := 4983230072969 + 3 ^ 40 * 2559077 * 2
def baseEnd_2559077 : Nat := 1314036532865989333168525

theorem tailTrace_2559077 : CollatzResearch.WordTrace tailWord_2559077 prefixEnd_2559077 1314036532865989333168525 := by
  unfold tailWord_2559077
  simp only [CollatzResearch.WordTrace]
  refine ⟨93337206149908559400939485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62224804099939039600626323 93337206149908559400939485)
  ·
    refine ⟨35001452306215709775352307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93337206149908559400939485 35001452306215709775352307)
    ·
      refine ⟨52502178459323564663028461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35001452306215709775352307 52502178459323564663028461)
      ·
        refine ⟨19688316922246336748635673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52502178459323564663028461 19688316922246336748635673)
        ·
          refine ⟨14766237691684752561476755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19688316922246336748635673 14766237691684752561476755)
          ·
            refine ⟨22149356537527128842215133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14766237691684752561476755 22149356537527128842215133)
            ·
              refine ⟨8306008701572673315830675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22149356537527128842215133 8306008701572673315830675)
              ·
                refine ⟨12459013052359009973746013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8306008701572673315830675 12459013052359009973746013)
                ·
                  refine ⟨4672129894634628740154755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12459013052359009973746013 4672129894634628740154755)
                  ·
                    refine ⟨7008194841951943110232133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4672129894634628740154755 7008194841951943110232133)
                    ·
                      refine ⟨1314036532865989333168525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7008194841951943110232133 1314036532865989333168525)
                      ·
                        rfl

theorem cell23_2559077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_2559077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559077 prefixEnd_2559077 := by exact prefixLift 2559077
  have htrace : WordTrace (prefixWord ++ tailWord_2559077) baseStart_2559077 baseEnd_2559077 := by
    simpa [prefixWord, tailWord_2559077, baseEnd_2559077] using wordTrace_append hprefix tailTrace_2559077
  have hstable : (prefixWord ++ tailWord_2559077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559077).length < 2 ^ (prefixWord ++ tailWord_2559077).sum := by decide
  have hdescent : baseEnd_2559077 < baseStart_2559077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559105 : List Nat := [1, 2, 4, 2, 2, 3, 2, 2, 1, 1, 3]
def baseStart_2559105 : Nat := 118140960795 + 2559105 * 2 ^ 59
def prefixEnd_2559105 : Nat := 4983230072969 + 3 ^ 40 * 2559105 * 2
def baseEnd_2559105 : Nat := 1314050910324315223618397

theorem tailTrace_2559105 : CollatzResearch.WordTrace tailWord_2559105 prefixEnd_2559105 1314050910324315223618397 := by
  unfold tailWord_2559105
  simp only [CollatzResearch.WordTrace]
  refine ⟨93338227393807120182958769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62225484929204746788639179 93338227393807120182958769)
  ·
    refine ⟨70003670545355340137219077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93338227393807120182958769 70003670545355340137219077)
    ·
      refine ⟨13125688227254126275728577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70003670545355340137219077 13125688227254126275728577)
      ·
        refine ⟨9844266170440594706796433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13125688227254126275728577 9844266170440594706796433)
        ·
          refine ⟨7383199627830446030097325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9844266170440594706796433 7383199627830446030097325)
          ·
            refine ⟨2768699860436417261286497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7383199627830446030097325 2768699860436417261286497)
            ·
              refine ⟨2076524895327312945964873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2768699860436417261286497 2076524895327312945964873)
              ·
                refine ⟨1557393671495484709473655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2076524895327312945964873 1557393671495484709473655)
                ·
                  refine ⟨2336090507243227064210483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1557393671495484709473655 2336090507243227064210483)
                  ·
                    refine ⟨3504135760864840596315725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2336090507243227064210483 3504135760864840596315725)
                    ·
                      refine ⟨1314050910324315223618397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3504135760864840596315725 1314050910324315223618397)
                      ·
                        rfl

theorem cell23_2559105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_2559105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559105 prefixEnd_2559105 := by exact prefixLift 2559105
  have htrace : WordTrace (prefixWord ++ tailWord_2559105) baseStart_2559105 baseEnd_2559105 := by
    simpa [prefixWord, tailWord_2559105, baseEnd_2559105] using wordTrace_append hprefix tailTrace_2559105
  have hstable : (prefixWord ++ tailWord_2559105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559105).length < 2 ^ (prefixWord ++ tailWord_2559105).sum := by decide
  have hdescent : baseEnd_2559105 < baseStart_2559105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559161 : List Nat := [1, 2, 1, 4, 1, 3, 3, 2, 2, 1, 3]
def baseStart_2559161 : Nat := 118140960795 + 2559161 * 2 ^ 59
def prefixEnd_2559161 : Nat := 4983230072969 + 3 ^ 40 * 2559161 * 2
def baseEnd_2559161 : Nat := 1314079665240967004518139

theorem tailTrace_2559161 : CollatzResearch.WordTrace tailWord_2559161 prefixEnd_2559161 1314079665240967004518139 := by
  unfold tailWord_2559161
  simp only [CollatzResearch.WordTrace]
  refine ⟨93340269881604241746997337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62226846587736161164664891 93340269881604241746997337)
  ·
    refine ⟨70005202411203181310248003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93340269881604241746997337 70005202411203181310248003)
    ·
      refine ⟨105007803616804771965372005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70005202411203181310248003 105007803616804771965372005)
      ·
        refine ⟨19688963178150894743507251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105007803616804771965372005 19688963178150894743507251)
        ·
          refine ⟨29533444767226342115260877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19688963178150894743507251 29533444767226342115260877)
          ·
            refine ⟨11075041787709878293222829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29533444767226342115260877 11075041787709878293222829)
            ·
              refine ⟨4153140670391204359958561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11075041787709878293222829 4153140670391204359958561)
              ·
                refine ⟨3114855502793403269968921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4153140670391204359958561 3114855502793403269968921)
                ·
                  refine ⟨2336141627095052452476691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3114855502793403269968921 2336141627095052452476691)
                  ·
                    refine ⟨3504212440642578678715037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2336141627095052452476691 3504212440642578678715037)
                    ·
                      refine ⟨1314079665240967004518139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3504212440642578678715037 1314079665240967004518139)
                      ·
                        rfl

theorem cell23_2559161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_2559161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559161 prefixEnd_2559161 := by exact prefixLift 2559161
  have htrace : WordTrace (prefixWord ++ tailWord_2559161) baseStart_2559161 baseEnd_2559161 := by
    simpa [prefixWord, tailWord_2559161, baseEnd_2559161] using wordTrace_append hprefix tailTrace_2559161
  have hstable : (prefixWord ++ tailWord_2559161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559161).length < 2 ^ (prefixWord ++ tailWord_2559161).sum := by decide
  have hdescent : baseEnd_2559161 < baseStart_2559161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559178 : List Nat := [3, 1, 2, 1, 3, 3, 3, 1, 2, 1, 3]
def baseStart_2559178 : Nat := 118140960795 + 2559178 * 2 ^ 59
def prefixEnd_2559178 : Nat := 4983230072969 + 3 ^ 40 * 2559178 * 2
def baseEnd_2559178 : Nat := 1314088394412093438005561

theorem tailTrace_2559178 : CollatzResearch.WordTrace tailWord_2559178 prefixEnd_2559178 1314088394412093438005561 := by
  unfold tailWord_2559178
  simp only [CollatzResearch.WordTrace]
  refine ⟨23335222480635663412591547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62227259948361769100244125 23335222480635663412591547)
  ·
    refine ⟨35002833720953495118887321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23335222480635663412591547 35002833720953495118887321)
    ·
      refine ⟨26252125290715121339165491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35002833720953495118887321 26252125290715121339165491)
      ·
        refine ⟨39378187936072682008748237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26252125290715121339165491 39378187936072682008748237)
        ·
          refine ⟨14766820476027255753280589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39378187936072682008748237 14766820476027255753280589)
          ·
            refine ⟨5537557678510220907480221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14766820476027255753280589 5537557678510220907480221)
            ·
              refine ⟨2076584129441332840305083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5537557678510220907480221 2076584129441332840305083)
              ·
                refine ⟨3114876194161999260457625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2076584129441332840305083 3114876194161999260457625)
                ·
                  refine ⟨2336157145621499445343219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3114876194161999260457625 2336157145621499445343219)
                  ·
                    refine ⟨3504235718432249168014829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2336157145621499445343219 3504235718432249168014829)
                    ·
                      refine ⟨1314088394412093438005561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3504235718432249168014829 1314088394412093438005561)
                      ·
                        rfl

theorem cell23_2559178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 2, 1, 3].length) (baseStart_2559178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559178 prefixEnd_2559178 := by exact prefixLift 2559178
  have htrace : WordTrace (prefixWord ++ tailWord_2559178) baseStart_2559178 baseEnd_2559178 := by
    simpa [prefixWord, tailWord_2559178, baseEnd_2559178] using wordTrace_append hprefix tailTrace_2559178
  have hstable : (prefixWord ++ tailWord_2559178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559178).length < 2 ^ (prefixWord ++ tailWord_2559178).sum := by decide
  have hdescent : baseEnd_2559178 < baseStart_2559178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559201 : List Nat := [1, 2, 3, 1, 3, 2, 1, 2, 4, 2, 2]
def baseStart_2559201 : Nat := 118140960795 + 2559201 * 2 ^ 59
def prefixEnd_2559201 : Nat := 4983230072969 + 3 ^ 40 * 2559201 * 2
def baseEnd_2559201 : Nat := 1314100204467146848017955

theorem tailTrace_2559201 : CollatzResearch.WordTrace tailWord_2559201 prefixEnd_2559201 1314100204467146848017955 := by
  unfold tailWord_2559201
  simp only [CollatzResearch.WordTrace]
  refine ⟨93341728801459328578453457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62227819200972885718968971 93341728801459328578453457)
  ·
    refine ⟨70006296601094496433840093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93341728801459328578453457 70006296601094496433840093)
    ·
      refine ⟨26252361225410436162690035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70006296601094496433840093 26252361225410436162690035)
      ·
        refine ⟨39378541838115654244035053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26252361225410436162690035 39378541838115654244035053)
        ·
          refine ⟨14766953189293370341513145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39378541838115654244035053 14766953189293370341513145)
          ·
            refine ⟨11075214891970027756134859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14766953189293370341513145 11075214891970027756134859)
            ·
              refine ⟨16612822337955041634202289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11075214891970027756134859 16612822337955041634202289)
              ·
                refine ⟨12459616753466281225651717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16612822337955041634202289 12459616753466281225651717)
                ·
                  refine ⟨2336178141274927729809697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12459616753466281225651717 2336178141274927729809697)
                  ·
                    refine ⟨1752133605956195797357273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2336178141274927729809697 1752133605956195797357273)
                    ·
                      refine ⟨1314100204467146848017955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1752133605956195797357273 1314100204467146848017955)
                      ·
                        rfl

theorem cell23_2559201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4, 2, 2].length) (baseStart_2559201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559201 prefixEnd_2559201 := by exact prefixLift 2559201
  have htrace : WordTrace (prefixWord ++ tailWord_2559201) baseStart_2559201 baseEnd_2559201 := by
    simpa [prefixWord, tailWord_2559201, baseEnd_2559201] using wordTrace_append hprefix tailTrace_2559201
  have hstable : (prefixWord ++ tailWord_2559201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559201).length < 2 ^ (prefixWord ++ tailWord_2559201).sum := by decide
  have hdescent : baseEnd_2559201 < baseStart_2559201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559235 : List Nat := [1, 1, 1, 3, 2, 6, 2, 1, 2, 2, 2]
def baseStart_2559235 : Nat := 118140960795 + 2559235 * 2 ^ 59
def prefixEnd_2559235 : Nat := 4983230072969 + 3 ^ 40 * 2559235 * 2
def baseEnd_2559235 : Nat := 1314117662809399714992799

theorem tailTrace_2559235 : CollatzResearch.WordTrace tailWord_2559235 prefixEnd_2559235 1314117662809399714992799 := by
  unfold tailWord_2559235
  simp only [CollatzResearch.WordTrace]
  refine ⟨93342968883336152385191159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62228645922224101590127439 93342968883336152385191159)
  ·
    refine ⟨140014453325004228577786739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93342968883336152385191159 140014453325004228577786739)
    ·
      refine ⟨210021679987506342866680109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140014453325004228577786739 210021679987506342866680109)
      ·
        refine ⟨78758129995314878575005041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210021679987506342866680109 78758129995314878575005041)
        ·
          refine ⟨59068597496486158931253781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78758129995314878575005041 59068597496486158931253781)
          ·
            refine ⟨2768840507647788699902521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 59068597496486158931253781 2768840507647788699902521)
            ·
              refine ⟨2076630380735841524926891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2768840507647788699902521 2076630380735841524926891)
              ·
                refine ⟨3114945571103762287390337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2076630380735841524926891 3114945571103762287390337)
                ·
                  refine ⟨2336209178327821715542753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3114945571103762287390337 2336209178327821715542753)
                  ·
                    refine ⟨1752156883745866286657065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2336209178327821715542753 1752156883745866286657065)
                    ·
                      refine ⟨1314117662809399714992799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1752156883745866286657065 1314117662809399714992799)
                      ·
                        rfl

theorem cell23_2559235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 2, 2, 2].length) (baseStart_2559235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559235 prefixEnd_2559235 := by exact prefixLift 2559235
  have htrace : WordTrace (prefixWord ++ tailWord_2559235) baseStart_2559235 baseEnd_2559235 := by
    simpa [prefixWord, tailWord_2559235, baseEnd_2559235] using wordTrace_append hprefix tailTrace_2559235
  have hstable : (prefixWord ++ tailWord_2559235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559235).length < 2 ^ (prefixWord ++ tailWord_2559235).sum := by decide
  have hdescent : baseEnd_2559235 < baseStart_2559235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559237 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 4, 5]
def baseStart_2559237 : Nat := 118140960795 + 2559237 * 2 ^ 59
def prefixEnd_2559237 : Nat := 4983230072969 + 3 ^ 40 * 2559237 * 2
def baseEnd_2559237 : Nat := 438039563256902902389263

theorem tailTrace_2559237 : CollatzResearch.WordTrace tailWord_2559237 prefixEnd_2559237 438039563256902902389263 := by
  unfold tailWord_2559237
  simp only [CollatzResearch.WordTrace]
  refine ⟨93343041829328906726763965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62228694552885937817842643 93343041829328906726763965)
  ·
    refine ⟨35003640685998340022536487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93343041829328906726763965 35003640685998340022536487)
    ·
      refine ⟨52505461028997510033804731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35003640685998340022536487 52505461028997510033804731)
      ·
        refine ⟨78758191543496265050707097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52505461028997510033804731 78758191543496265050707097)
        ·
          refine ⟨59068643657622198788030323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78758191543496265050707097 59068643657622198788030323)
          ·
            refine ⟨88602965486433298182045485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59068643657622198788030323 88602965486433298182045485)
            ·
              refine ⟨33226112057412486818267057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88602965486433298182045485 33226112057412486818267057)
              ·
                refine ⟨24919584043059365113700293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33226112057412486818267057 24919584043059365113700293)
                ·
                  refine ⟨4672422008073630958818805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24919584043059365113700293 4672422008073630958818805)
                  ·
                    refine ⟨438039563256902902389263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4672422008073630958818805 438039563256902902389263)
                    ·
                      rfl

theorem cell23_2559237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 5].length) (baseStart_2559237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559237 prefixEnd_2559237 := by exact prefixLift 2559237
  have htrace : WordTrace (prefixWord ++ tailWord_2559237) baseStart_2559237 baseEnd_2559237 := by
    simpa [prefixWord, tailWord_2559237, baseEnd_2559237] using wordTrace_append hprefix tailTrace_2559237
  have hstable : (prefixWord ++ tailWord_2559237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559237).length < 2 ^ (prefixWord ++ tailWord_2559237).sum := by decide
  have hdescent : baseEnd_2559237 < baseStart_2559237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559287 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 4]
def baseStart_2559287 : Nat := 118140960795 + 2559287 * 2 ^ 59
def prefixEnd_2559287 : Nat := 4983230072969 + 3 ^ 40 * 2559287 * 2
def baseEnd_2559287 : Nat := 1314144363803433511542559

theorem tailTrace_2559287 : CollatzResearch.WordTrace tailWord_2559287 prefixEnd_2559287 1314144363803433511542559 := by
  unfold tailWord_2559287
  simp only [CollatzResearch.WordTrace]
  refine ⟨93344865479147765266084115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62229910319431843510722743 93344865479147765266084115)
  ·
    refine ⟨140017298218721647899126173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93344865479147765266084115 140017298218721647899126173)
    ·
      refine ⟨52506486832020617962172315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140017298218721647899126173 52506486832020617962172315)
      ·
        refine ⟨78759730248030926943258473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52506486832020617962172315 78759730248030926943258473)
        ·
          refine ⟨59069797686023195207443855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78759730248030926943258473 59069797686023195207443855)
          ·
            refine ⟨88604696529034792811165783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59069797686023195207443855 88604696529034792811165783)
            ·
              refine ⟨132907044793552189216748675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88604696529034792811165783 132907044793552189216748675)
              ·
                refine ⟨199360567190328283825123013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132907044793552189216748675 199360567190328283825123013)
                ·
                  refine ⟨37380106348186553217210565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 199360567190328283825123013 37380106348186553217210565)
                  ·
                    refine ⟨7008769940284978728226981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37380106348186553217210565 7008769940284978728226981)
                    ·
                      refine ⟨1314144363803433511542559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7008769940284978728226981 1314144363803433511542559)
                      ·
                        rfl

theorem cell23_2559287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_2559287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559287 prefixEnd_2559287 := by exact prefixLift 2559287
  have htrace : WordTrace (prefixWord ++ tailWord_2559287) baseStart_2559287 baseEnd_2559287 := by
    simpa [prefixWord, tailWord_2559287, baseEnd_2559287] using wordTrace_append hprefix tailTrace_2559287
  have hstable : (prefixWord ++ tailWord_2559287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559287).length < 2 ^ (prefixWord ++ tailWord_2559287).sum := by decide
  have hdescent : baseEnd_2559287 < baseStart_2559287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559331 : List Nat := [1, 1, 1, 5, 2, 4, 1, 2, 6]
def baseStart_2559331 : Nat := 118140960795 + 2559331 * 2 ^ 59
def prefixEnd_2559331 : Nat := 4983230072969 + 3 ^ 40 * 2559331 * 2
def baseEnd_2559331 : Nat := 146018550772470148821373

theorem tailTrace_2559331 : CollatzResearch.WordTrace tailWord_2559331 prefixEnd_2559331 146018550772470148821373 := by
  unfold tailWord_2559331
  simp only [CollatzResearch.WordTrace]
  refine ⟨93346470290988360780685847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62230980193992240520457231 93346470290988360780685847)
  ·
    refine ⟨140019705436482541171028771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93346470290988360780685847 140019705436482541171028771)
    ·
      refine ⟨210029558154723811756543157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140019705436482541171028771 210029558154723811756543157)
      ·
        refine ⟨19690271077005357352175921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 210029558154723811756543157 19690271077005357352175921)
        ·
          refine ⟨14767703307754018014131941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19690271077005357352175921 14767703307754018014131941)
          ·
            refine ⟨2768944370203878377649739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14767703307754018014131941 2768944370203878377649739)
            ·
              refine ⟨4153416555305817566474609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2768944370203878377649739 4153416555305817566474609)
              ·
                refine ⟨3115062416479363174855957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4153416555305817566474609 3115062416479363174855957)
                ·
                  refine ⟨146018550772470148821373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3115062416479363174855957 146018550772470148821373)
                  ·
                    rfl

theorem cell23_2559331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 6].length) (baseStart_2559331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559331 prefixEnd_2559331 := by exact prefixLift 2559331
  have htrace : WordTrace (prefixWord ++ tailWord_2559331) baseStart_2559331 baseEnd_2559331 := by
    simpa [prefixWord, tailWord_2559331, baseEnd_2559331] using wordTrace_append hprefix tailTrace_2559331
  have hstable : (prefixWord ++ tailWord_2559331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559331).length < 2 ^ (prefixWord ++ tailWord_2559331).sum := by decide
  have hdescent : baseEnd_2559331 < baseStart_2559331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559337 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 2, 1, 7]
def baseStart_2559337 : Nat := 118140960795 + 2559337 * 2 ^ 59
def prefixEnd_2559337 : Nat := 4983230072969 + 3 ^ 40 * 2559337 * 2
def baseEnd_2559337 : Nat := 1314170037836158315917329

theorem tailTrace_2559337 : CollatzResearch.WordTrace tailWord_2559337 prefixEnd_2559337 1314170037836158315917329 := by
  unfold tailWord_2559337
  simp only [CollatzResearch.WordTrace]
  refine ⟨93346689128966623805404265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62231126085977749203602843 93346689128966623805404265)
  ·
    refine ⟨70010016846724967854053199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93346689128966623805404265 70010016846724967854053199)
    ·
      refine ⟨105015025270087451781079799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70010016846724967854053199 105015025270087451781079799)
      ·
        refine ⟨157522537905131177671619699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105015025270087451781079799 157522537905131177671619699)
        ·
          refine ⟨236283806857696766507429549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157522537905131177671619699 236283806857696766507429549)
          ·
            refine ⟨88606427571636287440286081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 236283806857696766507429549 88606427571636287440286081)
            ·
              refine ⟨66454820678727215580214561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88606427571636287440286081 66454820678727215580214561)
              ·
                refine ⟨49841115509045411685160921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66454820678727215580214561 49841115509045411685160921)
                ·
                  refine ⟨37380836631784058763870691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49841115509045411685160921 37380836631784058763870691)
                  ·
                    refine ⟨56071254947676088145806037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37380836631784058763870691 56071254947676088145806037)
                    ·
                      refine ⟨1314170037836158315917329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56071254947676088145806037 1314170037836158315917329)
                      ·
                        rfl

theorem cell23_2559337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 1, 7].length) (baseStart_2559337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559337 prefixEnd_2559337 := by exact prefixLift 2559337
  have htrace : WordTrace (prefixWord ++ tailWord_2559337) baseStart_2559337 baseEnd_2559337 := by
    simpa [prefixWord, tailWord_2559337, baseEnd_2559337] using wordTrace_append hprefix tailTrace_2559337
  have hstable : (prefixWord ++ tailWord_2559337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559337).length < 2 ^ (prefixWord ++ tailWord_2559337).sum := by decide
  have hdescent : baseEnd_2559337 < baseStart_2559337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559381 : List Nat := [1, 3, 2, 1, 1, 2, 4, 3, 1, 1, 4]
def baseStart_2559381 : Nat := 118140960795 + 2559381 * 2 ^ 59
def prefixEnd_2559381 : Nat := 4983230072969 + 3 ^ 40 * 2559381 * 2
def baseEnd_2559381 : Nat := 1314192630984956143767127

theorem tailTrace_2559381 : CollatzResearch.WordTrace tailWord_2559381 prefixEnd_2559381 1314192630984956143767127 := by
  unfold tailWord_2559381
  simp only [CollatzResearch.WordTrace]
  refine ⟨93348293940807219320005997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62232195960538146213337331 93348293940807219320005997)
  ·
    refine ⟨35005610227802707245002249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93348293940807219320005997 35005610227802707245002249)
    ·
      refine ⟨26254207670852030433751687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35005610227802707245002249 26254207670852030433751687)
      ·
        refine ⟨39381311506278045650627531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26254207670852030433751687 39381311506278045650627531)
        ·
          refine ⟨59071967259417068475941297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39381311506278045650627531 59071967259417068475941297)
          ·
            refine ⟨44303975444562801356955973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59071967259417068475941297 44303975444562801356955973)
            ·
              refine ⟨8306995395855525254429245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44303975444562801356955973 8306995395855525254429245)
              ·
                refine ⟨3115123273445821970410967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8306995395855525254429245 3115123273445821970410967)
                ·
                  refine ⟨4672684910168732955616451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3115123273445821970410967 4672684910168732955616451)
                  ·
                    refine ⟨7009027365253099433424677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4672684910168732955616451 7009027365253099433424677)
                    ·
                      refine ⟨1314192630984956143767127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7009027365253099433424677 1314192630984956143767127)
                      ·
                        rfl

theorem cell23_2559381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_2559381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559381 prefixEnd_2559381 := by exact prefixLift 2559381
  have htrace : WordTrace (prefixWord ++ tailWord_2559381) baseStart_2559381 baseEnd_2559381 := by
    simpa [prefixWord, tailWord_2559381, baseEnd_2559381] using wordTrace_append hprefix tailTrace_2559381
  have hstable : (prefixWord ++ tailWord_2559381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559381).length < 2 ^ (prefixWord ++ tailWord_2559381).sum := by decide
  have hdescent : baseEnd_2559381 < baseStart_2559381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559391 : List Nat := [1, 1, 2, 5, 1, 2, 2, 1, 4, 4]
def baseStart_2559391 : Nat := 118140960795 + 2559391 * 2 ^ 59
def prefixEnd_2559391 : Nat := 4983230072969 + 3 ^ 40 * 2559391 * 2
def baseEnd_2559391 : Nat := 438065921930500368214027

theorem tailTrace_2559391 : CollatzResearch.WordTrace tailWord_2559391 prefixEnd_2559391 438065921930500368214027 := by
  unfold tailWord_2559391
  simp only [CollatzResearch.WordTrace]
  refine ⟨93348658670770991027870027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62232439113847327351913351 93348658670770991027870027)
  ·
    refine ⟨140022988006156486541805041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93348658670770991027870027 140022988006156486541805041)
    ·
      refine ⟨105017241004617364906353781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140022988006156486541805041 105017241004617364906353781)
      ·
        refine ⟨9845366344182877959970667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105017241004617364906353781 9845366344182877959970667)
        ·
          refine ⟨14768049516274316939956001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9845366344182877959970667 14768049516274316939956001)
          ·
            refine ⟨11076037137205737704967001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14768049516274316939956001 11076037137205737704967001)
            ·
              refine ⟨8307027852904303278725251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11076037137205737704967001 8307027852904303278725251)
              ·
                refine ⟨12460541779356454918087877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8307027852904303278725251 12460541779356454918087877)
                ·
                  refine ⟨2336351583629335297141477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12460541779356454918087877 2336351583629335297141477)
                  ·
                    refine ⟨438065921930500368214027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2336351583629335297141477 438065921930500368214027)
                    ·
                      rfl

theorem cell23_2559391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4, 4].length) (baseStart_2559391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559391 prefixEnd_2559391 := by exact prefixLift 2559391
  have htrace : WordTrace (prefixWord ++ tailWord_2559391) baseStart_2559391 baseEnd_2559391 := by
    simpa [prefixWord, tailWord_2559391, baseEnd_2559391] using wordTrace_append hprefix tailTrace_2559391
  have hstable : (prefixWord ++ tailWord_2559391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559391).length < 2 ^ (prefixWord ++ tailWord_2559391).sum := by decide
  have hdescent : baseEnd_2559391 < baseStart_2559391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559428 : List Nat := [2, 3, 3, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_2559428 : Nat := 118140960795 + 2559428 * 2 ^ 59
def prefixEnd_2559428 : Nat := 4983230072969 + 3 ^ 40 * 2559428 * 2
def baseEnd_2559428 : Nat := 1314216764575717459879411

theorem tailTrace_2559428 : CollatzResearch.WordTrace tailWord_2559428 prefixEnd_2559428 1314216764575717459879411 := by
  unfold tailWord_2559428
  simp only [CollatzResearch.WordTrace]
  refine ⟨46675004085818473173483469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62233338781091297564644625 46675004085818473173483469)
  ·
    refine ⟨17503126532181927440056301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46675004085818473173483469 17503126532181927440056301)
    ·
      refine ⟨6563672449568222790021113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17503126532181927440056301 6563672449568222790021113)
      ·
        refine ⟨4922754337176167092515835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6563672449568222790021113 4922754337176167092515835)
        ·
          refine ⟨7384131505764250638773753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4922754337176167092515835 7384131505764250638773753)
          ·
            refine ⟨5538098629323187979080315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7384131505764250638773753 5538098629323187979080315)
            ·
              refine ⟨8307147943984781968620473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5538098629323187979080315 8307147943984781968620473)
              ·
                refine ⟨6230360957988586476465355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8307147943984781968620473 6230360957988586476465355)
                ·
                  refine ⟨9345541436982879714698033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6230360957988586476465355 9345541436982879714698033)
                  ·
                    refine ⟨7009156077737159786023525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9345541436982879714698033 7009156077737159786023525)
                    ·
                      refine ⟨1314216764575717459879411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7009156077737159786023525 1314216764575717459879411)
                      ·
                        rfl

theorem cell23_2559428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_2559428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559428 prefixEnd_2559428 := by exact prefixLift 2559428
  have htrace : WordTrace (prefixWord ++ tailWord_2559428) baseStart_2559428 baseEnd_2559428 := by
    simpa [prefixWord, tailWord_2559428, baseEnd_2559428] using wordTrace_append hprefix tailTrace_2559428
  have hstable : (prefixWord ++ tailWord_2559428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559428).length < 2 ^ (prefixWord ++ tailWord_2559428).sum := by decide
  have hdescent : baseEnd_2559428 < baseStart_2559428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559431 : List Nat := [1, 1, 4, 1, 1, 3, 3, 2, 1, 3, 3]
def baseStart_2559431 : Nat := 118140960795 + 2559431 * 2 ^ 59
def prefixEnd_2559431 : Nat := 4983230072969 + 3 ^ 40 * 2559431 * 2
def baseEnd_2559431 : Nat := 1314218305017680948141897

theorem tailTrace_2559431 : CollatzResearch.WordTrace tailWord_2559431 prefixEnd_2559431 1314218305017680948141897 := by
  unfold tailWord_2559431
  simp only [CollatzResearch.WordTrace]
  refine ⟨93350117590626077859326147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62233411727084051906217431 93350117590626077859326147)
  ·
    refine ⟨140025176385939116788989221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93350117590626077859326147 140025176385939116788989221)
    ·
      refine ⟨26254720572363584397935479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140025176385939116788989221 26254720572363584397935479)
      ·
        refine ⟨39382080858545376596903219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26254720572363584397935479 39382080858545376596903219)
        ·
          refine ⟨59073121287818064895354829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39382080858545376596903219 59073121287818064895354829)
          ·
            refine ⟨22152420482931774335758061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59073121287818064895354829 22152420482931774335758061)
            ·
              refine ⟨8307157681099415375909273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22152420482931774335758061 8307157681099415375909273)
              ·
                refine ⟨6230368260824561531931955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8307157681099415375909273 6230368260824561531931955)
                ·
                  refine ⟨9345552391236842297897933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6230368260824561531931955 9345552391236842297897933)
                  ·
                    refine ⟨3504582146713815861711725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9345552391236842297897933 3504582146713815861711725)
                    ·
                      refine ⟨1314218305017680948141897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3504582146713815861711725 1314218305017680948141897)
                      ·
                        rfl

theorem cell23_2559431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_2559431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559431 prefixEnd_2559431 := by exact prefixLift 2559431
  have htrace : WordTrace (prefixWord ++ tailWord_2559431) baseStart_2559431 baseEnd_2559431 := by
    simpa [prefixWord, tailWord_2559431, baseEnd_2559431] using wordTrace_append hprefix tailTrace_2559431
  have hstable : (prefixWord ++ tailWord_2559431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559431).length < 2 ^ (prefixWord ++ tailWord_2559431).sum := by decide
  have hdescent : baseEnd_2559431 < baseStart_2559431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559448 : List Nat := [2, 1, 2, 2, 2, 1, 3, 4, 2, 1, 3]
def baseStart_2559448 : Nat := 118140960795 + 2559448 * 2 ^ 59
def prefixEnd_2559448 : Nat := 4983230072969 + 3 ^ 40 * 2559448 * 2
def baseEnd_2559448 : Nat := 1314227034188807381629319

theorem tailTrace_2559448 : CollatzResearch.WordTrace tailWord_2559448 prefixEnd_2559448 1314227034188807381629319 := by
  unfold tailWord_2559448
  simp only [CollatzResearch.WordTrace]
  refine ⟨46675368815782244881347499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62233825087709659841796665 46675368815782244881347499)
  ·
    refine ⟨70013053223673367322021249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46675368815782244881347499 70013053223673367322021249)
    ·
      refine ⟨52509789917755025491515937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70013053223673367322021249 52509789917755025491515937)
      ·
        refine ⟨39382342438316269118636953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52509789917755025491515937 39382342438316269118636953)
        ·
          refine ⟨29536756828737201838977715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39382342438316269118636953 29536756828737201838977715)
          ·
            refine ⟨44305135243105802758466573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29536756828737201838977715 44305135243105802758466573)
            ·
              refine ⟨16614425716164676034424965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44305135243105802758466573 16614425716164676034424965)
              ·
                refine ⟨3115204821780876756454681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16614425716164676034424965 3115204821780876756454681)
                ·
                  refine ⟨2336403616335657567341011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3115204821780876756454681 2336403616335657567341011)
                  ·
                    refine ⟨3504605424503486351011517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2336403616335657567341011 3504605424503486351011517)
                    ·
                      refine ⟨1314227034188807381629319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3504605424503486351011517 1314227034188807381629319)
                      ·
                        rfl

theorem cell23_2559448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_2559448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559448 prefixEnd_2559448 := by exact prefixLift 2559448
  have htrace : WordTrace (prefixWord ++ tailWord_2559448) baseStart_2559448 baseEnd_2559448 := by
    simpa [prefixWord, tailWord_2559448, baseEnd_2559448] using wordTrace_append hprefix tailTrace_2559448
  have hstable : (prefixWord ++ tailWord_2559448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559448).length < 2 ^ (prefixWord ++ tailWord_2559448).sum := by decide
  have hdescent : baseEnd_2559448 < baseStart_2559448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559449 : List Nat := [1, 2, 1, 2, 4, 4, 2, 2, 1, 2, 2]
def baseStart_2559449 : Nat := 118140960795 + 2559449 * 2 ^ 59
def prefixEnd_2559449 : Nat := 4983230072969 + 3 ^ 40 * 2559449 * 2
def baseEnd_2559449 : Nat := 1314227547669461877716815

theorem tailTrace_2559449 : CollatzResearch.WordTrace tailWord_2559449 prefixEnd_2559449 1314227547669461877716815 := by
  unfold tailWord_2559449
  simp only [CollatzResearch.WordTrace]
  refine ⟨93350774104560866933481401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62233849403040577955654267 93350774104560866933481401)
  ·
    refine ⟨70013080578420650200111051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93350774104560866933481401 70013080578420650200111051)
    ·
      refine ⟨105019620867630975300166577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70013080578420650200111051 105019620867630975300166577)
      ·
        refine ⟨78764715650723231475124933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105019620867630975300166577 78764715650723231475124933)
        ·
          refine ⟨14768384184510605901585925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78764715650723231475124933 14768384184510605901585925)
          ·
            refine ⟨2769072034595738606547361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14768384184510605901585925 2769072034595738606547361)
            ·
              refine ⟨2076804025946803954910521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2769072034595738606547361 2076804025946803954910521)
              ·
                refine ⟨1557603019460102966182891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2076804025946803954910521 1557603019460102966182891)
                ·
                  refine ⟨2336404529190154449274337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1557603019460102966182891 2336404529190154449274337)
                  ·
                    refine ⟨1752303396892615836955753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2336404529190154449274337 1752303396892615836955753)
                    ·
                      refine ⟨1314227547669461877716815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1752303396892615836955753 1314227547669461877716815)
                      ·
                        rfl

theorem cell23_2559449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2, 1, 2, 2].length) (baseStart_2559449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559449 prefixEnd_2559449 := by exact prefixLift 2559449
  have htrace : WordTrace (prefixWord ++ tailWord_2559449) baseStart_2559449 baseEnd_2559449 := by
    simpa [prefixWord, tailWord_2559449, baseEnd_2559449] using wordTrace_append hprefix tailTrace_2559449
  have hstable : (prefixWord ++ tailWord_2559449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559449).length < 2 ^ (prefixWord ++ tailWord_2559449).sum := by decide
  have hdescent : baseEnd_2559449 < baseStart_2559449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559486 : List Nat := [4, 2, 2, 3, 2, 1, 2, 1, 1, 2, 3]
def baseStart_2559486 : Nat := 118140960795 + 2559486 * 2 ^ 59
def prefixEnd_2559486 : Nat := 4983230072969 + 3 ^ 40 * 2559486 * 2
def baseEnd_2559486 : Nat := 1314246546453678232954145

theorem tailTrace_2559486 : CollatzResearch.WordTrace tailWord_2559486 prefixEnd_2559486 1314246546453678232954145 := by
  unfold tailWord_2559486
  simp only [CollatzResearch.WordTrace]
  refine ⟨11669015450678352781572289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62234749070284548168385541 11669015450678352781572289)
  ·
    refine ⟨8751761588008764586179217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11669015450678352781572289 8751761588008764586179217)
    ·
      refine ⟨6563821191006573439634413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8751761588008764586179217 6563821191006573439634413)
      ·
        refine ⟨2461432946627465039862905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6563821191006573439634413 2461432946627465039862905)
        ·
          refine ⟨1846074709970598779897179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2461432946627465039862905 1846074709970598779897179)
          ·
            refine ⟨2769112064955898169845769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1846074709970598779897179 2769112064955898169845769)
            ·
              refine ⟨2076834048716923627384327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2769112064955898169845769 2076834048716923627384327)
              ·
                refine ⟨3115251073075385441076491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2076834048716923627384327 3115251073075385441076491)
                ·
                  refine ⟨4672876609613078161614737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3115251073075385441076491 4672876609613078161614737)
                  ·
                    refine ⟨3504657457209808621211053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4672876609613078161614737 3504657457209808621211053)
                    ·
                      refine ⟨1314246546453678232954145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3504657457209808621211053 1314246546453678232954145)
                      ·
                        rfl

theorem cell23_2559486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_2559486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559486 prefixEnd_2559486 := by exact prefixLift 2559486
  have htrace : WordTrace (prefixWord ++ tailWord_2559486) baseStart_2559486 baseEnd_2559486 := by
    simpa [prefixWord, tailWord_2559486, baseEnd_2559486] using wordTrace_append hprefix tailTrace_2559486
  have hstable : (prefixWord ++ tailWord_2559486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559486).length < 2 ^ (prefixWord ++ tailWord_2559486).sum := by decide
  have hdescent : baseEnd_2559486 < baseStart_2559486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559492 : List Nat := [2, 3, 2, 3, 2, 1, 1, 3, 1, 3, 2]
def baseStart_2559492 : Nat := 118140960795 + 2559492 * 2 ^ 59
def prefixEnd_2559492 : Nat := 4983230072969 + 3 ^ 40 * 2559492 * 2
def baseEnd_2559492 : Nat := 1314249627337605209479117

theorem tailTrace_2559492 : CollatzResearch.WordTrace tailWord_2559492 prefixEnd_2559492 1314249627337605209479117 := by
  unfold tailWord_2559492
  simp only [CollatzResearch.WordTrace]
  refine ⟨46676171221702542638648365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62234894962270056851531153 46676171221702542638648365)
  ·
    refine ⟨17503564208138453489493137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46676171221702542638648365 17503564208138453489493137)
    ·
      refine ⟨13127673156103840117119853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17503564208138453489493137 13127673156103840117119853)
      ·
        refine ⟨4922877433538940043919945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13127673156103840117119853 4922877433538940043919945)
        ·
          refine ⟨3692158075154205032939959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4922877433538940043919945 3692158075154205032939959)
          ·
            refine ⟨5538237112731307549409939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3692158075154205032939959 5538237112731307549409939)
            ·
              refine ⟨8307355669096961324114909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5538237112731307549409939 8307355669096961324114909)
              ·
                refine ⟨3115258375911360496543091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8307355669096961324114909 3115258375911360496543091)
                ·
                  refine ⟨4672887563867040744814637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3115258375911360496543091 4672887563867040744814637)
                  ·
                    refine ⟨1752332836450140279305489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4672887563867040744814637 1752332836450140279305489)
                    ·
                      refine ⟨1314249627337605209479117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1752332836450140279305489 1314249627337605209479117)
                      ·
                        rfl

theorem cell23_2559492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_2559492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559492 prefixEnd_2559492 := by exact prefixLift 2559492
  have htrace : WordTrace (prefixWord ++ tailWord_2559492) baseStart_2559492 baseEnd_2559492 := by
    simpa [prefixWord, tailWord_2559492, baseEnd_2559492] using wordTrace_append hprefix tailTrace_2559492
  have hstable : (prefixWord ++ tailWord_2559492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559492).length < 2 ^ (prefixWord ++ tailWord_2559492).sum := by decide
  have hdescent : baseEnd_2559492 < baseStart_2559492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559541 : List Nat := [1, 3, 3, 1, 1, 3, 2, 1, 1, 7]
def baseStart_2559541 : Nat := 118140960795 + 2559541 * 2 ^ 59
def prefixEnd_2559541 : Nat := 4983230072969 + 3 ^ 40 * 2559541 * 2
def baseEnd_2559541 : Nat := 438091595963225172588797

theorem tailTrace_2559541 : CollatzResearch.WordTrace tailWord_2559541 prefixEnd_2559541 438091595963225172588797 := by
  unfold tailWord_2559541
  simp only [CollatzResearch.WordTrace]
  refine ⟨93354129620227566645830477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62236086413485044430553651 93354129620227566645830477)
  ·
    refine ⟨35007798607585337492186429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93354129620227566645830477 35007798607585337492186429)
    ·
      refine ⟨13127924477844501559569911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35007798607585337492186429 13127924477844501559569911)
      ·
        refine ⟨19691886716766752339354867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13127924477844501559569911 19691886716766752339354867)
        ·
          refine ⟨29537830075150128509032301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19691886716766752339354867 29537830075150128509032301)
          ·
            refine ⟨11076686278181298190887113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29537830075150128509032301 11076686278181298190887113)
            ·
              refine ⟨8307514708635973643165335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11076686278181298190887113 8307514708635973643165335)
              ·
                refine ⟨12461272062953960464748003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8307514708635973643165335 12461272062953960464748003)
                ·
                  refine ⟨18691908094430940697122005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12461272062953960464748003 18691908094430940697122005)
                  ·
                    refine ⟨438091595963225172588797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18691908094430940697122005 438091595963225172588797)
                    ·
                      rfl

theorem cell23_2559541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_2559541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559541 prefixEnd_2559541 := by exact prefixLift 2559541
  have htrace : WordTrace (prefixWord ++ tailWord_2559541) baseStart_2559541 baseEnd_2559541 := by
    simpa [prefixWord, tailWord_2559541, baseEnd_2559541] using wordTrace_append hprefix tailTrace_2559541
  have hstable : (prefixWord ++ tailWord_2559541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559541).length < 2 ^ (prefixWord ++ tailWord_2559541).sum := by decide
  have hdescent : baseEnd_2559541 < baseStart_2559541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559545 : List Nat := [1, 2, 1, 5, 1, 4, 1, 3, 5]
def baseStart_2559545 : Nat := 118140960795 + 2559545 * 2 ^ 59
def prefixEnd_2559545 : Nat := 4983230072969 + 3 ^ 40 * 2559545 * 2
def baseEnd_2559545 : Nat := 146030760201365944679597

theorem tailTrace_2559545 : CollatzResearch.WordTrace tailWord_2559545 prefixEnd_2559545 146030760201365944679597 := by
  unfold tailWord_2559545
  simp only [CollatzResearch.WordTrace]
  refine ⟨93354275512213075328976089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62236183674808716885984059 93354275512213075328976089)
  ·
    refine ⟨70015706634159806496732067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93354275512213075328976089 70015706634159806496732067)
    ·
      refine ⟨105023559951239709745098101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70015706634159806496732067 105023559951239709745098101)
      ·
        refine ⟨9845958745428722788602947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105023559951239709745098101 9845958745428722788602947)
        ·
          refine ⟨14768938118143084182904421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9845958745428722788602947 14768938118143084182904421)
          ·
            refine ⟨2769175897151828284294579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14768938118143084182904421 2769175897151828284294579)
            ·
              refine ⟨4153763845727742426441869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2769175897151828284294579 4153763845727742426441869)
              ·
                refine ⟨1557661442147903409915701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4153763845727742426441869 1557661442147903409915701)
                ·
                  refine ⟨146030760201365944679597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1557661442147903409915701 146030760201365944679597)
                  ·
                    rfl

theorem cell23_2559545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3, 5].length) (baseStart_2559545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559545 prefixEnd_2559545 := by exact prefixLift 2559545
  have htrace : WordTrace (prefixWord ++ tailWord_2559545) baseStart_2559545 baseEnd_2559545 := by
    simpa [prefixWord, tailWord_2559545, baseEnd_2559545] using wordTrace_append hprefix tailTrace_2559545
  have hstable : (prefixWord ++ tailWord_2559545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559545).length < 2 ^ (prefixWord ++ tailWord_2559545).sum := by decide
  have hdescent : baseEnd_2559545 < baseStart_2559545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559571 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 9, 4]
def baseStart_2559571 : Nat := 118140960795 + 2559571 * 2 ^ 59
def prefixEnd_2559571 : Nat := 4983230072969 + 3 ^ 40 * 2559571 * 2
def baseEnd_2559571 : Nat := 438096730769770133463751

theorem tailTrace_2559571 : CollatzResearch.WordTrace tailWord_2559571 prefixEnd_2559571 438096730769770133463751 := by
  unfold tailWord_2559571
  simp only [CollatzResearch.WordTrace]
  refine ⟨93355223810118881769422567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62236815873412587846281711 93355223810118881769422567)
  ·
    refine ⟨140032835715178322654133851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93355223810118881769422567 140032835715178322654133851)
    ·
      refine ⟨210049253572767483981200777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140032835715178322654133851 210049253572767483981200777)
      ·
        refine ⟨157536940179575612985900583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210049253572767483981200777 157536940179575612985900583)
        ·
          refine ⟨236305410269363419478850875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157536940179575612985900583 236305410269363419478850875)
          ·
            refine ⟨354458115404045129218276313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236305410269363419478850875 354458115404045129218276313)
            ·
              refine ⟨265843586553033846913707235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354458115404045129218276313 265843586553033846913707235)
              ·
                refine ⟨398765379829550770370560853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265843586553033846913707235 398765379829550770370560853)
                ·
                  refine ⟨2336515897438774045140005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 398765379829550770370560853 2336515897438774045140005)
                  ·
                    refine ⟨438096730769770133463751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2336515897438774045140005 438096730769770133463751)
                    ·
                      rfl

theorem cell23_2559571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9, 4].length) (baseStart_2559571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559571 prefixEnd_2559571 := by exact prefixLift 2559571
  have htrace : WordTrace (prefixWord ++ tailWord_2559571) baseStart_2559571 baseEnd_2559571 := by
    simpa [prefixWord, tailWord_2559571, baseEnd_2559571] using wordTrace_append hprefix tailTrace_2559571
  have hstable : (prefixWord ++ tailWord_2559571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559571).length < 2 ^ (prefixWord ++ tailWord_2559571).sum := by decide
  have hdescent : baseEnd_2559571 < baseStart_2559571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559578 : List Nat := [3, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2]
def baseStart_2559578 : Nat := 118140960795 + 2559578 * 2 ^ 59
def prefixEnd_2559578 : Nat := 4983230072969 + 3 ^ 40 * 2559578 * 2
def baseEnd_2559578 : Nat := 1314293786673891873003721

theorem tailTrace_2559578 : CollatzResearch.WordTrace tailWord_2559578 prefixEnd_2559578 1314293786673891873003721 := by
  unfold tailWord_2559578
  simp only [CollatzResearch.WordTrace]
  refine ⟨23338869780273380491231847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62236986080729014643284925 23338869780273380491231847)
  ·
    refine ⟨35008304670410070736847771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23338869780273380491231847 35008304670410070736847771)
    ·
      refine ⟨52512457005615106105271657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35008304670410070736847771 52512457005615106105271657)
      ·
        refine ⟨39384342754211329578953743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52512457005615106105271657 39384342754211329578953743)
        ·
          refine ⟨59076514131316994368430615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39384342754211329578953743 59076514131316994368430615)
          ·
            refine ⟨88614771196975491552645923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59076514131316994368430615 88614771196975491552645923)
            ·
              refine ⟨132922156795463237328968885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88614771196975491552645923 132922156795463237328968885)
              ·
                refine ⟨12461452199574678499590833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 132922156795463237328968885 12461452199574678499590833)
                ·
                  refine ⟨9346089149681008874693125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12461452199574678499590833 9346089149681008874693125)
                  ·
                    refine ⟨1752391715565189164004961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9346089149681008874693125 1752391715565189164004961)
                    ·
                      refine ⟨1314293786673891873003721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1752391715565189164004961 1314293786673891873003721)
                      ·
                        rfl

theorem cell23_2559578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2].length) (baseStart_2559578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559578 prefixEnd_2559578 := by exact prefixLift 2559578
  have htrace : WordTrace (prefixWord ++ tailWord_2559578) baseStart_2559578 baseEnd_2559578 := by
    simpa [prefixWord, tailWord_2559578, baseEnd_2559578] using wordTrace_append hprefix tailTrace_2559578
  have hstable : (prefixWord ++ tailWord_2559578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559578).length < 2 ^ (prefixWord ++ tailWord_2559578).sum := by decide
  have hdescent : baseEnd_2559578 < baseStart_2559578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559591 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_2559591 : Nat := 118140960795 + 2559591 * 2 ^ 59
def prefixEnd_2559591 : Nat := 4983230072969 + 3 ^ 40 * 2559591 * 2
def baseEnd_2559591 : Nat := 1314300461922400322141161

theorem tailTrace_2559591 : CollatzResearch.WordTrace tailWord_2559591 prefixEnd_2559591 1314300461922400322141161 := by
  unfold tailWord_2559591
  simp only [CollatzResearch.WordTrace]
  refine ⟨93355953270046425185150627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62237302180030950123433751 93355953270046425185150627)
  ·
    refine ⟨140033929905069637777725941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93355953270046425185150627 140033929905069637777725941)
    ·
      refine ⟨13128180928600278541661807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140033929905069637777725941 13128180928600278541661807)
      ·
        refine ⟨19692271392900417812492711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13128180928600278541661807 19692271392900417812492711)
        ·
          refine ⟨29538407089350626718739067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19692271392900417812492711 29538407089350626718739067)
          ·
            refine ⟨44307610634025940078108601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29538407089350626718739067 44307610634025940078108601)
            ·
              refine ⟨33230707975519455058581451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44307610634025940078108601 33230707975519455058581451)
              ·
                refine ⟨49846061963279182587872177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33230707975519455058581451 49846061963279182587872177)
                ·
                  refine ⟨37384546472459386940904133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49846061963279182587872177 37384546472459386940904133)
                  ·
                    refine ⟨7009602463586135051419525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37384546472459386940904133 7009602463586135051419525)
                    ·
                      refine ⟨1314300461922400322141161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7009602463586135051419525 1314300461922400322141161)
                      ·
                        rfl

theorem cell23_2559591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_2559591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559591 prefixEnd_2559591 := by exact prefixLift 2559591
  have htrace : WordTrace (prefixWord ++ tailWord_2559591) baseStart_2559591 baseEnd_2559591 := by
    simpa [prefixWord, tailWord_2559591, baseEnd_2559591] using wordTrace_append hprefix tailTrace_2559591
  have hstable : (prefixWord ++ tailWord_2559591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559591).length < 2 ^ (prefixWord ++ tailWord_2559591).sum := by decide
  have hdescent : baseEnd_2559591 < baseStart_2559591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559621 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 1, 2, 6]
def baseStart_2559621 : Nat := 118140960795 + 2559621 * 2 ^ 59
def prefixEnd_2559621 : Nat := 4983230072969 + 3 ^ 40 * 2559621 * 2
def baseEnd_2559621 : Nat := 1314315866342035204766023

theorem tailTrace_2559621 : CollatzResearch.WordTrace tailWord_2559621 prefixEnd_2559621 1314315866342035204766023 := by
  unfold tailWord_2559621
  simp only [CollatzResearch.WordTrace]
  refine ⟨93357047459937740308742717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62238031639958493539161811 93357047459937740308742717)
  ·
    refine ⟨35008892797476652615778519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93357047459937740308742717 35008892797476652615778519)
    ·
      refine ⟨52513339196214978923667779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35008892797476652615778519 52513339196214978923667779)
      ·
        refine ⟨78770008794322468385501669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52513339196214978923667779 78770008794322468385501669)
        ·
          refine ⟨14769376648935462822281563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78770008794322468385501669 14769376648935462822281563)
          ·
            refine ⟨22154064973403194233422345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14769376648935462822281563 22154064973403194233422345)
            ·
              refine ⟨16615548730052395675066759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22154064973403194233422345 16615548730052395675066759)
              ·
                refine ⟨24923323095078593512600139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16615548730052395675066759 24923323095078593512600139)
                ·
                  refine ⟨37384984642617890268900209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24923323095078593512600139 37384984642617890268900209)
                  ·
                    refine ⟨28038738481963417701675157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37384984642617890268900209 28038738481963417701675157)
                    ·
                      refine ⟨1314315866342035204766023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28038738481963417701675157 1314315866342035204766023)
                      ·
                        rfl

theorem cell23_2559621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_2559621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559621 prefixEnd_2559621 := by exact prefixLift 2559621
  have htrace : WordTrace (prefixWord ++ tailWord_2559621) baseStart_2559621 baseEnd_2559621 := by
    simpa [prefixWord, tailWord_2559621, baseEnd_2559621] using wordTrace_append hprefix tailTrace_2559621
  have hstable : (prefixWord ++ tailWord_2559621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559621).length < 2 ^ (prefixWord ++ tailWord_2559621).sum := by decide
  have hdescent : baseEnd_2559621 < baseStart_2559621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559648 : List Nat := [2, 1, 1, 4, 3, 1, 2, 1, 3, 5]
def baseStart_2559648 : Nat := 118140960795 + 2559648 * 2 ^ 59
def prefixEnd_2559648 : Nat := 4983230072969 + 3 ^ 40 * 2559648 * 2
def baseEnd_2559648 : Nat := 438109910106568866376133

theorem tailTrace_2559648 : CollatzResearch.WordTrace tailWord_2559648 prefixEnd_2559648 438109910106568866376133 := by
  unfold tailWord_2559648
  simp only [CollatzResearch.WordTrace]
  refine ⟨46679016115419961959987799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62238688153893282613317065 46679016115419961959987799)
  ·
    refine ⟨70018524173129942939981699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46679016115419961959987799 70018524173129942939981699)
    ·
      refine ⟨105027786259694914409972549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70018524173129942939981699 105027786259694914409972549)
      ·
        refine ⟨19692709923692796451869853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105027786259694914409972549 19692709923692796451869853)
        ·
          refine ⟨7384766221384798669451195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19692709923692796451869853 7384766221384798669451195)
          ·
            refine ⟨11077149332077198004176793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7384766221384798669451195 11077149332077198004176793)
            ·
              refine ⟨8307861999057898503132595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11077149332077198004176793 8307861999057898503132595)
              ·
                refine ⟨12461792998586847754698893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8307861999057898503132595 12461792998586847754698893)
                ·
                  refine ⟨4673172374470067908012085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12461792998586847754698893 4673172374470067908012085)
                  ·
                    refine ⟨438109910106568866376133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4673172374470067908012085 438109910106568866376133)
                    ·
                      rfl

theorem cell23_2559648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 3, 5].length) (baseStart_2559648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559648 prefixEnd_2559648 := by exact prefixLift 2559648
  have htrace : WordTrace (prefixWord ++ tailWord_2559648) baseStart_2559648 baseEnd_2559648 := by
    simpa [prefixWord, tailWord_2559648, baseEnd_2559648] using wordTrace_append hprefix tailTrace_2559648
  have hstable : (prefixWord ++ tailWord_2559648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559648).length < 2 ^ (prefixWord ++ tailWord_2559648).sum := by decide
  have hdescent : baseEnd_2559648 < baseStart_2559648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559685 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 7, 2, 2]
def baseStart_2559685 : Nat := 118140960795 + 2559685 * 2 ^ 59
def prefixEnd_2559685 : Nat := 4983230072969 + 3 ^ 40 * 2559685 * 2
def baseEnd_2559685 : Nat := 1314348729103922954365729

theorem tailTrace_2559685 : CollatzResearch.WordTrace tailWord_2559685 prefixEnd_2559685 1314348729103922954365729 := by
  unfold tailWord_2559685
  simp only [CollatzResearch.WordTrace]
  refine ⟨93359381731705879239072509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62239587821137252826048339 93359381731705879239072509)
  ·
    refine ⟨35009768149389704714652191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93359381731705879239072509 35009768149389704714652191)
    ·
      refine ⟨52514652224084557071978287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35009768149389704714652191 52514652224084557071978287)
      ·
        refine ⟨78771978336126835607967431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52514652224084557071978287 78771978336126835607967431)
        ·
          refine ⟨118157967504190253411951147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78771978336126835607967431 118157967504190253411951147)
          ·
            refine ⟨177236951256285380117926721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118157967504190253411951147 177236951256285380117926721)
            ·
              refine ⟨132927713442214035088445041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177236951256285380117926721 132927713442214035088445041)
              ·
                refine ⟨99695785081660526316333781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132927713442214035088445041 99695785081660526316333781)
                ·
                  refine ⟨2336619962851418585539073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 99695785081660526316333781 2336619962851418585539073)
                  ·
                    refine ⟨1752464972138563939154305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2336619962851418585539073 1752464972138563939154305)
                    ·
                      refine ⟨1314348729103922954365729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1752464972138563939154305 1314348729103922954365729)
                      ·
                        rfl

theorem cell23_2559685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7, 2, 2].length) (baseStart_2559685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559685 prefixEnd_2559685 := by exact prefixLift 2559685
  have htrace : WordTrace (prefixWord ++ tailWord_2559685) baseStart_2559685 baseEnd_2559685 := by
    simpa [prefixWord, tailWord_2559685, baseEnd_2559685] using wordTrace_append hprefix tailTrace_2559685
  have hstable : (prefixWord ++ tailWord_2559685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559685).length < 2 ^ (prefixWord ++ tailWord_2559685).sum := by decide
  have hdescent : baseEnd_2559685 < baseStart_2559685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559688 : List Nat := [2, 1, 3, 1, 2, 2, 3, 2, 1, 1, 5]
def baseStart_2559688 : Nat := 118140960795 + 2559688 * 2 ^ 59
def prefixEnd_2559688 : Nat := 4983230072969 + 3 ^ 40 * 2559688 * 2
def baseEnd_2559688 : Nat := 1314350269545886442628215

theorem tailTrace_2559688 : CollatzResearch.WordTrace tailWord_2559688 prefixEnd_2559688 1314350269545886442628215 := by
  unfold tailWord_2559688
  simp only [CollatzResearch.WordTrace]
  refine ⟨46679745575347505375715859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62239660767130007167621145 46679745575347505375715859)
  ·
    refine ⟨70019618363021258063573789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46679745575347505375715859 70019618363021258063573789)
    ·
      refine ⟨26257356886132971773840171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70019618363021258063573789 26257356886132971773840171)
      ·
        refine ⟨39386035329199457660760257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26257356886132971773840171 39386035329199457660760257)
        ·
          refine ⟨29539526496899593245570193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39386035329199457660760257 29539526496899593245570193)
          ·
            refine ⟨22154644872674694934177645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29539526496899593245570193 22154644872674694934177645)
            ·
              refine ⟨8307991827253010600316617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22154644872674694934177645 8307991827253010600316617)
              ·
                refine ⟨6230993870439757950237463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8307991827253010600316617 6230993870439757950237463)
                ·
                  refine ⟨9346490805659636925356195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6230993870439757950237463 9346490805659636925356195)
                  ·
                    refine ⟨14019736208489455388034293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9346490805659636925356195 14019736208489455388034293)
                    ·
                      refine ⟨1314350269545886442628215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14019736208489455388034293 1314350269545886442628215)
                      ·
                        rfl

theorem cell23_2559688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_2559688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559688 prefixEnd_2559688 := by exact prefixLift 2559688
  have htrace : WordTrace (prefixWord ++ tailWord_2559688) baseStart_2559688 baseEnd_2559688 := by
    simpa [prefixWord, tailWord_2559688, baseEnd_2559688] using wordTrace_append hprefix tailTrace_2559688
  have hstable : (prefixWord ++ tailWord_2559688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559688).length < 2 ^ (prefixWord ++ tailWord_2559688).sum := by decide
  have hdescent : baseEnd_2559688 < baseStart_2559688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559705 : List Nat := [1, 2, 1, 2, 3, 3, 1, 4, 1, 2, 3]
def baseStart_2559705 : Nat := 118140960795 + 2559705 * 2 ^ 59
def prefixEnd_2559705 : Nat := 4983230072969 + 3 ^ 40 * 2559705 * 2
def baseEnd_2559705 : Nat := 1314358998717012876115637

theorem tailTrace_2559705 : CollatzResearch.WordTrace tailWord_2559705 prefixEnd_2559705 1314358998717012876115637 := by
  unfold tailWord_2559705
  simp only [CollatzResearch.WordTrace]
  refine ⟨93360111191633422654800569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62240074127755615103200379 93360111191633422654800569)
  ·
    refine ⟨70020083393725066991100427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93360111191633422654800569 70020083393725066991100427)
    ·
      refine ⟨105030125090587600486650641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70020083393725066991100427 105030125090587600486650641)
      ·
        refine ⟨78772593817940700364987981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105030125090587600486650641 78772593817940700364987981)
        ·
          refine ⟨29539722681727762636870493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78772593817940700364987981 29539722681727762636870493)
          ·
            refine ⟨11077396005647910988826435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29539722681727762636870493 11077396005647910988826435)
            ·
              refine ⟨16616094008471866483239653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11077396005647910988826435 16616094008471866483239653)
              ·
                refine ⟨3115517626588474965607435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16616094008471866483239653 3115517626588474965607435)
                ·
                  refine ⟨4673276439882712448411153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3115517626588474965607435 4673276439882712448411153)
                  ·
                    refine ⟨3504957329912034336308365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4673276439882712448411153 3504957329912034336308365)
                    ·
                      refine ⟨1314358998717012876115637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3504957329912034336308365 1314358998717012876115637)
                      ·
                        rfl

theorem cell23_2559705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 2, 3].length) (baseStart_2559705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559705 prefixEnd_2559705 := by exact prefixLift 2559705
  have htrace : WordTrace (prefixWord ++ tailWord_2559705) baseStart_2559705 baseEnd_2559705 := by
    simpa [prefixWord, tailWord_2559705, baseEnd_2559705] using wordTrace_append hprefix tailTrace_2559705
  have hstable : (prefixWord ++ tailWord_2559705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559705).length < 2 ^ (prefixWord ++ tailWord_2559705).sum := by decide
  have hdescent : baseEnd_2559705 < baseStart_2559705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559721 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 1, 9]
def baseStart_2559721 : Nat := 118140960795 + 2559721 * 2 ^ 59
def prefixEnd_2559721 : Nat := 4983230072969 + 3 ^ 40 * 2559721 * 2
def baseEnd_2559721 : Nat := 438122404802494937838521

theorem tailTrace_2559721 : CollatzResearch.WordTrace tailWord_2559721 prefixEnd_2559721 438122404802494937838521 := by
  unfold tailWord_2559721
  simp only [CollatzResearch.WordTrace]
  refine ⟨93360694759575457387383017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62240463173050304924922011 93360694759575457387383017)
  ·
    refine ⟨70020521069681593040537263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93360694759575457387383017 70020521069681593040537263)
    ·
      refine ⟨105030781604522389560805895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70020521069681593040537263 105030781604522389560805895)
      ·
        refine ⟨157546172406783584341208843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105030781604522389560805895 157546172406783584341208843)
        ·
          refine ⟨236319258610175376511813265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157546172406783584341208843 236319258610175376511813265)
          ·
            refine ⟨177239443957631532383859949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236319258610175376511813265 177239443957631532383859949)
            ·
              refine ⟨66464791484111824643947481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177239443957631532383859949 66464791484111824643947481)
              ·
                refine ⟨49848593613083868482960611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66464791484111824643947481 49848593613083868482960611)
                ·
                  refine ⟨74772890419625802724440917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49848593613083868482960611 74772890419625802724440917)
                  ·
                    refine ⟨438122404802494937838521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 74772890419625802724440917 438122404802494937838521)
                    ·
                      rfl

theorem cell23_2559721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 9].length) (baseStart_2559721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559721 prefixEnd_2559721 := by exact prefixLift 2559721
  have htrace : WordTrace (prefixWord ++ tailWord_2559721) baseStart_2559721 baseEnd_2559721 := by
    simpa [prefixWord, tailWord_2559721, baseEnd_2559721] using wordTrace_append hprefix tailTrace_2559721
  have hstable : (prefixWord ++ tailWord_2559721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559721).length < 2 ^ (prefixWord ++ tailWord_2559721).sum := by decide
  have hdescent : baseEnd_2559721 < baseStart_2559721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559732 : List Nat := [2, 6, 1, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_2559732 : Nat := 118140960795 + 2559732 * 2 ^ 59
def prefixEnd_2559732 : Nat := 4983230072969 + 3 ^ 40 * 2559732 * 2
def baseEnd_2559732 : Nat := 1314372862694684270478013

theorem tailTrace_2559732 : CollatzResearch.WordTrace tailWord_2559732 prefixEnd_2559732 1314372862694684270478013 := by
  unfold tailWord_2559732
  simp only [CollatzResearch.WordTrace]
  refine ⟨46680547981267803133016725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62240730641690404177355633 46680547981267803133016725)
  ·
    refine ⟨2188150686621928271860159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 46680547981267803133016725 2188150686621928271860159)
    ·
      refine ⟨3282226029932892407790239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2188150686621928271860159 3282226029932892407790239)
      ·
        refine ⟨4923339044899338611685359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3282226029932892407790239 4923339044899338611685359)
        ·
          refine ⟨7385008567349007917528039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4923339044899338611685359 7385008567349007917528039)
          ·
            refine ⟨11077512851023511876292059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7385008567349007917528039 11077512851023511876292059)
            ·
              refine ⟨16616269276535267814438089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11077512851023511876292059 16616269276535267814438089)
              ·
                refine ⟨12462201957401450860828567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16616269276535267814438089 12462201957401450860828567)
                ·
                  refine ⟨18693302936102176291242851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12462201957401450860828567 18693302936102176291242851)
                  ·
                    refine ⟨28039954404153264436864277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18693302936102176291242851 28039954404153264436864277)
                    ·
                      refine ⟨1314372862694684270478013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28039954404153264436864277 1314372862694684270478013)
                      ·
                        rfl

theorem cell23_2559732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_2559732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559732 prefixEnd_2559732 := by exact prefixLift 2559732
  have htrace : WordTrace (prefixWord ++ tailWord_2559732) baseStart_2559732 baseEnd_2559732 := by
    simpa [prefixWord, tailWord_2559732, baseEnd_2559732] using wordTrace_append hprefix tailTrace_2559732
  have hstable : (prefixWord ++ tailWord_2559732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559732).length < 2 ^ (prefixWord ++ tailWord_2559732).sum := by decide
  have hdescent : baseEnd_2559732 < baseStart_2559732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559735 : List Nat := [1, 1, 3, 1, 1, 1, 6, 1, 4, 1, 3]
def baseStart_2559735 : Nat := 118140960795 + 2559735 * 2 ^ 59
def prefixEnd_2559735 : Nat := 4983230072969 + 3 ^ 40 * 2559735 * 2
def baseEnd_2559735 : Nat := 1314374403136647758740499

theorem tailTrace_2559735 : CollatzResearch.WordTrace tailWord_2559735 prefixEnd_2559735 1314374403136647758740499 := by
  unfold tailWord_2559735
  simp only [CollatzResearch.WordTrace]
  refine ⟨93361205381524737778392659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62240803587683158518928439 93361205381524737778392659)
  ·
    refine ⟨140041808072287106667588989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93361205381524737778392659 140041808072287106667588989)
    ·
      refine ⟨52515678027107665000345871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140041808072287106667588989 52515678027107665000345871)
      ·
        refine ⟨78773517040661497500518807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52515678027107665000345871 78773517040661497500518807)
        ·
          refine ⟨118160275560992246250778211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78773517040661497500518807 118160275560992246250778211)
          ·
            refine ⟨177240413341488369376167317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118160275560992246250778211 177240413341488369376167317)
            ·
              refine ⟨8308144375382267314507843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 177240413341488369376167317 8308144375382267314507843)
              ·
                refine ⟨12462216563073400971761765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8308144375382267314507843 12462216563073400971761765)
                ·
                  refine ⟨2336665605576262682205331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12462216563073400971761765 2336665605576262682205331)
                  ·
                    refine ⟨3504998408364394023307997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2336665605576262682205331 3504998408364394023307997)
                    ·
                      refine ⟨1314374403136647758740499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3504998408364394023307997 1314374403136647758740499)
                      ·
                        rfl

theorem cell23_2559735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4, 1, 3].length) (baseStart_2559735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559735 prefixEnd_2559735 := by exact prefixLift 2559735
  have htrace : WordTrace (prefixWord ++ tailWord_2559735) baseStart_2559735 baseEnd_2559735 := by
    simpa [prefixWord, tailWord_2559735, baseEnd_2559735] using wordTrace_append hprefix tailTrace_2559735
  have hstable : (prefixWord ++ tailWord_2559735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559735).length < 2 ^ (prefixWord ++ tailWord_2559735).sum := by decide
  have hdescent : baseEnd_2559735 < baseStart_2559735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559750 : List Nat := [6, 2, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_2559750 : Nat := 118140960795 + 2559750 * 2 ^ 59
def prefixEnd_2559750 : Nat := 4983230072969 + 3 ^ 40 * 2559750 * 2
def baseEnd_2559750 : Nat := 438127368448821733350977

theorem tailTrace_2559750 : CollatzResearch.WordTrace tailWord_2559750 prefixEnd_2559750 438127368448821733350977 := by
  unfold tailWord_2559750
  simp only [CollatzResearch.WordTrace]
  refine ⟨2917554764889699854380897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 62241168317646930226792469 2917554764889699854380897)
  ·
    refine ⟨2188166073667274890785673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2917554764889699854380897 2188166073667274890785673)
    ·
      refine ⟨1641124555250456168089255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2188166073667274890785673 1641124555250456168089255)
      ·
        refine ⟨2461686832875684252133883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1641124555250456168089255 2461686832875684252133883)
        ·
          refine ⟨3692530249313526378200825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2461686832875684252133883 3692530249313526378200825)
          ·
            refine ⟨2769397686985144783650619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3692530249313526378200825 2769397686985144783650619)
            ·
              refine ⟨4154096530477717175475929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2769397686985144783650619 4154096530477717175475929)
              ·
                refine ⟨3115572397858287881606947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4154096530477717175475929 3115572397858287881606947)
                ·
                  refine ⟨4673358596787431822410421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3115572397858287881606947 4673358596787431822410421)
                  ·
                    refine ⟨438127368448821733350977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4673358596787431822410421 438127368448821733350977)
                    ·
                      rfl

theorem cell23_2559750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_2559750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559750 prefixEnd_2559750 := by exact prefixLift 2559750
  have htrace : WordTrace (prefixWord ++ tailWord_2559750) baseStart_2559750 baseEnd_2559750 := by
    simpa [prefixWord, tailWord_2559750, baseEnd_2559750] using wordTrace_append hprefix tailTrace_2559750
  have hstable : (prefixWord ++ tailWord_2559750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559750).length < 2 ^ (prefixWord ++ tailWord_2559750).sum := by decide
  have hdescent : baseEnd_2559750 < baseStart_2559750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559752 : List Nat := [2, 1, 3, 2, 2, 1, 3, 3, 2, 1, 3]
def baseStart_2559752 : Nat := 118140960795 + 2559752 * 2 ^ 59
def prefixEnd_2559752 : Nat := 4983230072969 + 3 ^ 40 * 2559752 * 2
def baseEnd_2559752 : Nat := 1314383132307774192227921

theorem tailTrace_2559752 : CollatzResearch.WordTrace tailWord_2559752 prefixEnd_2559752 1314383132307774192227921 := by
  unfold tailWord_2559752
  simp only [CollatzResearch.WordTrace]
  refine ⟨46680912711231574840880755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62241216948308766454507673 46680912711231574840880755)
  ·
    refine ⟨70021369066847362261321133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46680912711231574840880755 70021369066847362261321133)
    ·
      refine ⟨26258013400067760847995425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70021369066847362261321133 26258013400067760847995425)
      ·
        refine ⟨19693510050050820635996569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26258013400067760847995425 19693510050050820635996569)
        ·
          refine ⟨14770132537538115476997427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19693510050050820635996569 14770132537538115476997427)
          ·
            refine ⟨22155198806307173215496141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14770132537538115476997427 22155198806307173215496141)
            ·
              refine ⟨8308199552365189955811053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22155198806307173215496141 8308199552365189955811053)
              ·
                refine ⟨3115574832136946233429145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8308199552365189955811053 3115574832136946233429145)
                ·
                  refine ⟨2336681124102709675071859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3115574832136946233429145 2336681124102709675071859)
                  ·
                    refine ⟨3505021686154064512607789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2336681124102709675071859 3505021686154064512607789)
                    ·
                      refine ⟨1314383132307774192227921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3505021686154064512607789 1314383132307774192227921)
                      ·
                        rfl

theorem cell23_2559752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_2559752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559752 prefixEnd_2559752 := by exact prefixLift 2559752
  have htrace : WordTrace (prefixWord ++ tailWord_2559752) baseStart_2559752 baseEnd_2559752 := by
    simpa [prefixWord, tailWord_2559752, baseEnd_2559752] using wordTrace_append hprefix tailTrace_2559752
  have hstable : (prefixWord ++ tailWord_2559752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559752).length < 2 ^ (prefixWord ++ tailWord_2559752).sum := by decide
  have hdescent : baseEnd_2559752 < baseStart_2559752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559805 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 1, 4, 4]
def baseStart_2559805 : Nat := 118140960795 + 2559805 * 2 ^ 59
def prefixEnd_2559805 : Nat := 4983230072969 + 3 ^ 40 * 2559805 * 2
def baseEnd_2559805 : Nat := 1314410346782462484865177

theorem tailTrace_2559805 : CollatzResearch.WordTrace tailWord_2559805 prefixEnd_2559805 1314410346782462484865177 := by
  unfold tailWord_2559805
  simp only [CollatzResearch.WordTrace]
  refine ⟨93363758491271139733440869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62242505660847426488960579 93363758491271139733440869)
  ·
    refine ⟨17505704717113338700020163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93363758491271139733440869 17505704717113338700020163)
    ·
      refine ⟨26258557075670008050030245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17505704717113338700020163 26258557075670008050030245)
      ·
        refine ⟨4923479451688126509380671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26258557075670008050030245 4923479451688126509380671)
        ·
          refine ⟨7385219177532189764071007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4923479451688126509380671 7385219177532189764071007)
          ·
            refine ⟨11077828766298284646106511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7385219177532189764071007 11077828766298284646106511)
            ·
              refine ⟨16616743149447426969159767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11077828766298284646106511 16616743149447426969159767)
              ·
                refine ⟨24925114724171140453739651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16616743149447426969159767 24925114724171140453739651)
                ·
                  refine ⟨37387672086256710680609477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24925114724171140453739651 37387672086256710680609477)
                  ·
                    refine ⟨7010188516173133252614277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37387672086256710680609477 7010188516173133252614277)
                    ·
                      refine ⟨1314410346782462484865177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7010188516173133252614277 1314410346782462484865177)
                      ·
                        rfl

theorem cell23_2559805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_2559805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559805 prefixEnd_2559805 := by exact prefixLift 2559805
  have htrace : WordTrace (prefixWord ++ tailWord_2559805) baseStart_2559805 baseEnd_2559805 := by
    simpa [prefixWord, tailWord_2559805, baseEnd_2559805] using wordTrace_append hprefix tailTrace_2559805
  have hstable : (prefixWord ++ tailWord_2559805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559805).length < 2 ^ (prefixWord ++ tailWord_2559805).sum := by decide
  have hdescent : baseEnd_2559805 < baseStart_2559805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559842 : List Nat := [3, 3, 2, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_2559842 : Nat := 118140960795 + 2559842 * 2 ^ 59
def prefixEnd_2559842 : Nat := 4983230072969 + 3 ^ 40 * 2559842 * 2
def baseEnd_2559842 : Nat := 1314429345566678840102507

theorem tailTrace_2559842 : CollatzResearch.WordTrace tailWord_2559842 prefixEnd_2559842 1314429345566678840102507 := by
  unfold tailWord_2559842
  simp only [CollatzResearch.WordTrace]
  refine ⟨23341276998034273763134445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62243405328091396701691853 23341276998034273763134445)
  ·
    refine ⟨8752978874262852661175417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23341276998034273763134445 8752978874262852661175417)
    ·
      refine ⟨6564734155697139495881563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8752978874262852661175417 6564734155697139495881563)
      ·
        refine ⟨9847101233545709243822345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6564734155697139495881563 9847101233545709243822345)
        ·
          refine ⟨7385325925159281932866759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9847101233545709243822345 7385325925159281932866759)
          ·
            refine ⟨11077988887738922899300139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7385325925159281932866759 11077988887738922899300139)
            ·
              refine ⟨16616983331608384348950209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11077988887738922899300139 16616983331608384348950209)
              ·
                refine ⟨12462737498706288261712657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16616983331608384348950209 12462737498706288261712657)
                ·
                  refine ⟨9347053124029716196284493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12462737498706288261712657 9347053124029716196284493)
                  ·
                    refine ⟨3505144921511143573606685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9347053124029716196284493 3505144921511143573606685)
                    ·
                      refine ⟨1314429345566678840102507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3505144921511143573606685 1314429345566678840102507)
                      ·
                        rfl

theorem cell23_2559842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_2559842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559842 prefixEnd_2559842 := by exact prefixLift 2559842
  have htrace : WordTrace (prefixWord ++ tailWord_2559842) baseStart_2559842 baseEnd_2559842 := by
    simpa [prefixWord, tailWord_2559842, baseEnd_2559842] using wordTrace_append hprefix tailTrace_2559842
  have hstable : (prefixWord ++ tailWord_2559842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559842).length < 2 ^ (prefixWord ++ tailWord_2559842).sum := by decide
  have hdescent : baseEnd_2559842 < baseStart_2559842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559843 : List Nat := [1, 1, 1, 5, 5, 1, 1, 2, 2, 2, 2]
def baseStart_2559843 : Nat := 118140960795 + 2559843 * 2 ^ 59
def prefixEnd_2559843 : Nat := 4983230072969 + 3 ^ 40 * 2559843 * 2
def baseEnd_2559843 : Nat := 1314429859047333336190003

theorem tailTrace_2559843 : CollatzResearch.WordTrace tailWord_2559843 prefixEnd_2559843 1314429859047333336190003 := by
  unfold tailWord_2559843
  simp only [CollatzResearch.WordTrace]
  refine ⟨93365144465133472223324183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62243429643422314815549455 93365144465133472223324183)
  ·
    refine ⟨140047716697700208334986275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93365144465133472223324183 140047716697700208334986275)
    ·
      refine ⟨210071575046550312502479413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140047716697700208334986275 210071575046550312502479413)
      ·
        refine ⟨19694210160614091797107445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 210071575046550312502479413 19694210160614091797107445)
        ·
          refine ⟨1846332202557571105978823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19694210160614091797107445 1846332202557571105978823)
          ·
            refine ⟨2769498303836356658968235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1846332202557571105978823 2769498303836356658968235)
            ·
              refine ⟨4154247455754534988452353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2769498303836356658968235 4154247455754534988452353)
              ·
                refine ⟨3115685591815901241339265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4154247455754534988452353 3115685591815901241339265)
                ·
                  refine ⟨2336764193861925931004449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3115685591815901241339265 2336764193861925931004449)
                  ·
                    refine ⟨1752573145396444448253337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2336764193861925931004449 1752573145396444448253337)
                    ·
                      refine ⟨1314429859047333336190003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1752573145396444448253337 1314429859047333336190003)
                      ·
                        rfl

theorem cell23_2559843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_2559843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559843 prefixEnd_2559843 := by exact prefixLift 2559843
  have htrace : WordTrace (prefixWord ++ tailWord_2559843) baseStart_2559843 baseEnd_2559843 := by
    simpa [prefixWord, tailWord_2559843, baseEnd_2559843] using wordTrace_append hprefix tailTrace_2559843
  have hstable : (prefixWord ++ tailWord_2559843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559843).length < 2 ^ (prefixWord ++ tailWord_2559843).sum := by decide
  have hdescent : baseEnd_2559843 < baseStart_2559843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559888 : List Nat := [2, 1, 1, 1, 1, 1, 2, 6, 8]
def baseStart_2559888 : Nat := 118140960795 + 2559888 * 2 ^ 59
def prefixEnd_2559888 : Nat := 4983230072969 + 3 ^ 40 * 2559888 * 2
def baseEnd_2559888 : Nat := 146050329519642851125255

theorem tailTrace_2559888 : CollatzResearch.WordTrace tailWord_2559888 prefixEnd_2559888 146050329519642851125255 := by
  unfold tailWord_2559888
  simp only [CollatzResearch.WordTrace]
  refine ⟨46683392874985222454356159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62244523833313629939141545 46683392874985222454356159)
  ·
    refine ⟨70025089312477833681534239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46683392874985222454356159 70025089312477833681534239)
    ·
      refine ⟨105037633968716750522301359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70025089312477833681534239 105037633968716750522301359)
      ·
        refine ⟨157556450953075125783452039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105037633968716750522301359 157556450953075125783452039)
        ·
          refine ⟨236334676429612688675178059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157556450953075125783452039 236334676429612688675178059)
          ·
            refine ⟨354502014644419033012767089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236334676429612688675178059 354502014644419033012767089)
            ·
              refine ⟨265876510983314274759575317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354502014644419033012767089 265876510983314274759575317)
              ·
                refine ⟨12462961452342856629355093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 265876510983314274759575317 12462961452342856629355093)
                ·
                  refine ⟨146050329519642851125255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12462961452342856629355093 146050329519642851125255)
                  ·
                    rfl

theorem cell23_2559888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 8].length) (baseStart_2559888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559888 prefixEnd_2559888 := by exact prefixLift 2559888
  have htrace : WordTrace (prefixWord ++ tailWord_2559888) baseStart_2559888 baseEnd_2559888 := by
    simpa [prefixWord, tailWord_2559888, baseEnd_2559888] using wordTrace_append hprefix tailTrace_2559888
  have hstable : (prefixWord ++ tailWord_2559888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559888).length < 2 ^ (prefixWord ++ tailWord_2559888).sum := by decide
  have hdescent : baseEnd_2559888 < baseStart_2559888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559935 : List Nat := [1, 1, 2, 2, 2, 1, 5, 1, 3, 5]
def baseStart_2559935 : Nat := 118140960795 + 2559935 * 2 ^ 59
def prefixEnd_2559935 : Nat := 4983230072969 + 3 ^ 40 * 2559935 * 2
def baseEnd_2559935 : Nat := 438159033089182325413193

theorem tailTrace_2559935 : CollatzResearch.WordTrace tailWord_2559935 prefixEnd_2559935 438159033089182325413193 := by
  unfold tailWord_2559935
  simp only [CollatzResearch.WordTrace]
  refine ⟨93368499980800171935673259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62245666653866781290448839 93368499980800171935673259)
  ·
    refine ⟨140052749971200257903509889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93368499980800171935673259 140052749971200257903509889)
    ·
      refine ⟨105039562478400193427632417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140052749971200257903509889 105039562478400193427632417)
      ·
        refine ⟨78779671858800145070724313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105039562478400193427632417 78779671858800145070724313)
        ·
          refine ⟨59084753894100108803043235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78779671858800145070724313 59084753894100108803043235)
          ·
            refine ⟨88627130841150163204564853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59084753894100108803043235 88627130841150163204564853)
            ·
              refine ⟨8308793516357827800427955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88627130841150163204564853 8308793516357827800427955)
              ·
                refine ⟨12463190274536741700641933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8308793516357827800427955 12463190274536741700641933)
                ·
                  refine ⟨4673696352951278137740725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12463190274536741700641933 4673696352951278137740725)
                  ·
                    refine ⟨438159033089182325413193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4673696352951278137740725 438159033089182325413193)
                    ·
                      rfl

theorem cell23_2559935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 5].length) (baseStart_2559935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559935 prefixEnd_2559935 := by exact prefixLift 2559935
  have htrace : WordTrace (prefixWord ++ tailWord_2559935) baseStart_2559935 baseEnd_2559935 := by
    simpa [prefixWord, tailWord_2559935, baseEnd_2559935] using wordTrace_append hprefix tailTrace_2559935
  have hstable : (prefixWord ++ tailWord_2559935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559935).length < 2 ^ (prefixWord ++ tailWord_2559935).sum := by decide
  have hdescent : baseEnd_2559935 < baseStart_2559935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559982 : List Nat := [4, 1, 2, 1, 3, 1, 1, 3, 1, 6]
def baseStart_2559982 : Nat := 118140960795 + 2559982 * 2 ^ 59
def prefixEnd_2559982 : Nat := 4983230072969 + 3 ^ 40 * 2559982 * 2
def baseEnd_2559982 : Nat := 438167077619436097450621

theorem tailTrace_2559982 : CollatzResearch.WordTrace tailWord_2559982 prefixEnd_2559982 438167077619436097450621 := by
  unfold tailWord_2559982
  simp only [CollatzResearch.WordTrace]
  refine ⟨11671276776453737370329275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62246809474419932641756133 11671276776453737370329275)
  ·
    refine ⟨17506915164680606055493913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11671276776453737370329275 17506915164680606055493913)
    ·
      refine ⟨13130186373510454541620435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17506915164680606055493913 13130186373510454541620435)
      ·
        refine ⟨19695279560265681812430653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13130186373510454541620435 19695279560265681812430653)
        ·
          refine ⟨7385729835099630679661495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19695279560265681812430653 7385729835099630679661495)
          ·
            refine ⟨11078594752649446019492243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7385729835099630679661495 11078594752649446019492243)
            ·
              refine ⟨16617892128974169029238365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11078594752649446019492243 16617892128974169029238365)
              ·
                refine ⟨6231709548365313385964387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16617892128974169029238365 6231709548365313385964387)
                ·
                  refine ⟨9347564322547970078946581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6231709548365313385964387 9347564322547970078946581)
                  ·
                    refine ⟨438167077619436097450621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9347564322547970078946581 438167077619436097450621)
                    ·
                      rfl

theorem cell23_2559982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_2559982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559982 prefixEnd_2559982 := by exact prefixLift 2559982
  have htrace : WordTrace (prefixWord ++ tailWord_2559982) baseStart_2559982 baseEnd_2559982 := by
    simpa [prefixWord, tailWord_2559982, baseEnd_2559982] using wordTrace_append hprefix tailTrace_2559982
  have hstable : (prefixWord ++ tailWord_2559982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559982).length < 2 ^ (prefixWord ++ tailWord_2559982).sum := by decide
  have hdescent : baseEnd_2559982 < baseStart_2559982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2559992 : List Nat := [2, 1, 2, 1, 1, 3, 4, 1, 3, 2, 3]
def baseStart_2559992 : Nat := 118140960795 + 2559992 * 2 ^ 59
def prefixEnd_2559992 : Nat := 4983230072969 + 3 ^ 40 * 2559992 * 2
def baseEnd_2559992 : Nat := 1314506367664853253226817

theorem tailTrace_2559992 : CollatzResearch.WordTrace tailWord_2559992 prefixEnd_2559992 1314506367664853253226817 := by
  unfold tailWord_2559992
  simp only [CollatzResearch.WordTrace]
  refine ⟨46685289470796835335249115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62247052627729113780332153 46685289470796835335249115)
  ·
    refine ⟨70027934206195253002873673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46685289470796835335249115 70027934206195253002873673)
    ·
      refine ⟨52520950654646439752155255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70027934206195253002873673 52520950654646439752155255)
      ·
        refine ⟨78781425981969659628232883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52520950654646439752155255 78781425981969659628232883)
        ·
          refine ⟨118172138972954489442349325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78781425981969659628232883 118172138972954489442349325)
          ·
            refine ⟨44314552114857933540880997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118172138972954489442349325 44314552114857933540880997)
            ·
              refine ⟨8308978521535862538915187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44314552114857933540880997 8308978521535862538915187)
              ·
                refine ⟨12463467782303793808372781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8308978521535862538915187 12463467782303793808372781)
                ·
                  refine ⟨4673800418363922678139793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12463467782303793808372781 4673800418363922678139793)
                  ·
                    refine ⟨3505350313772942008604845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4673800418363922678139793 3505350313772942008604845)
                    ·
                      refine ⟨1314506367664853253226817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3505350313772942008604845 1314506367664853253226817)
                      ·
                        rfl

theorem cell23_2559992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 3, 2, 3].length) (baseStart_2559992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2559992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2559992 prefixEnd_2559992 := by exact prefixLift 2559992
  have htrace : WordTrace (prefixWord ++ tailWord_2559992) baseStart_2559992 baseEnd_2559992 := by
    simpa [prefixWord, tailWord_2559992, baseEnd_2559992] using wordTrace_append hprefix tailTrace_2559992
  have hstable : (prefixWord ++ tailWord_2559992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2559992).length < 2 ^ (prefixWord ++ tailWord_2559992).sum := by decide
  have hdescent : baseEnd_2559992 < baseStart_2559992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2559992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560023 : List Nat := [1, 1, 3, 5, 2, 1, 2, 1, 3, 2, 2]
def baseStart_2560023 : Nat := 118140960795 + 2560023 * 2 ^ 59
def prefixEnd_2560023 : Nat := 4983230072969 + 3 ^ 40 * 2560023 * 2
def baseEnd_2560023 : Nat := 1314522285565142631939175

theorem tailTrace_2560023 : CollatzResearch.WordTrace tailWord_2560023 prefixEnd_2560023 1314522285565142631939175 := by
  unfold tailWord_2560023
  simp only [CollatzResearch.WordTrace]
  refine ⟨93371709604481362964876723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62247806402987575309917815 93371709604481362964876723)
  ·
    refine ⟨140057564406722044447315085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93371709604481362964876723 140057564406722044447315085)
    ·
      refine ⟨52521586652520766667743157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140057564406722044447315085 52521586652520766667743157)
      ·
        refine ⟨4923898748673821875100921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52521586652520766667743157 4923898748673821875100921)
        ·
          refine ⟨3692924061505366406325691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4923898748673821875100921 3692924061505366406325691)
          ·
            refine ⟨5539386092258049609488537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3692924061505366406325691 5539386092258049609488537)
            ·
              refine ⟨4154539569193537207116403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5539386092258049609488537 4154539569193537207116403)
              ·
                refine ⟨6231809353790305810674605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4154539569193537207116403 6231809353790305810674605)
                ·
                  refine ⟨2336928507671364679002977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6231809353790305810674605 2336928507671364679002977)
                  ·
                    refine ⟨1752696380753523509252233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2336928507671364679002977 1752696380753523509252233)
                    ·
                      refine ⟨1314522285565142631939175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1752696380753523509252233 1314522285565142631939175)
                      ·
                        rfl

theorem cell23_2560023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_2560023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560023 prefixEnd_2560023 := by exact prefixLift 2560023
  have htrace : WordTrace (prefixWord ++ tailWord_2560023) baseStart_2560023 baseEnd_2560023 := by
    simpa [prefixWord, tailWord_2560023, baseEnd_2560023] using wordTrace_append hprefix tailTrace_2560023
  have hstable : (prefixWord ++ tailWord_2560023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560023).length < 2 ^ (prefixWord ++ tailWord_2560023).sum := by decide
  have hdescent : baseEnd_2560023 < baseStart_2560023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560036 : List Nat := [2, 3, 1, 4, 2, 2, 1, 1, 1, 2, 4]
def baseStart_2560036 : Nat := 118140960795 + 2560036 * 2 ^ 59
def prefixEnd_2560036 : Nat := 4983230072969 + 3 ^ 40 * 2560036 * 2
def baseEnd_2560036 : Nat := 1314528960813651081076615

theorem tailTrace_2560036 : CollatzResearch.WordTrace tailWord_2560036 prefixEnd_2560036 1314528960813651081076615 := by
  unfold tailWord_2560036
  simp only [CollatzResearch.WordTrace]
  refine ⟨46686091876717133092549981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62248122502289510790066641 46686091876717133092549981)
  ·
    refine ⟨17507284453768924909706243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46686091876717133092549981 17507284453768924909706243)
    ·
      refine ⟨26260926680653387364559365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17507284453768924909706243 26260926680653387364559365)
      ·
        refine ⟨4923923752622510130854881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26260926680653387364559365 4923923752622510130854881)
        ·
          refine ⟨3692942814466882598141161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4923923752622510130854881 3692942814466882598141161)
          ·
            refine ⟨2769707110850161948605871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3692942814466882598141161 2769707110850161948605871)
            ·
              refine ⟨4154560666275242922908807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2769707110850161948605871 4154560666275242922908807)
              ·
                refine ⟨6231840999412864384363211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4154560666275242922908807 6231840999412864384363211)
                ·
                  refine ⟨9347761499119296576544817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6231840999412864384363211 9347761499119296576544817)
                  ·
                    refine ⟨7010821124339472432408613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9347761499119296576544817 7010821124339472432408613)
                    ·
                      refine ⟨1314528960813651081076615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7010821124339472432408613 1314528960813651081076615)
                      ·
                        rfl

theorem cell23_2560036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_2560036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560036 prefixEnd_2560036 := by exact prefixLift 2560036
  have htrace : WordTrace (prefixWord ++ tailWord_2560036) baseStart_2560036 baseEnd_2560036 := by
    simpa [prefixWord, tailWord_2560036, baseEnd_2560036] using wordTrace_append hprefix tailTrace_2560036
  have hstable : (prefixWord ++ tailWord_2560036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560036).length < 2 ^ (prefixWord ++ tailWord_2560036).sum := by decide
  have hdescent : baseEnd_2560036 < baseStart_2560036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560055 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 1, 8]
def baseStart_2560055 : Nat := 118140960795 + 2560055 * 2 ^ 59
def prefixEnd_2560055 : Nat := 4983230072969 + 3 ^ 40 * 2560055 * 2
def baseEnd_2560055 : Nat := 438179572315362168913009

theorem tailTrace_2560055 : CollatzResearch.WordTrace tailWord_2560055 prefixEnd_2560055 438179572315362168913009 := by
  unfold tailWord_2560055
  simp only [CollatzResearch.WordTrace]
  refine ⟨93372876740365432430041619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62248584493576954953361079 93372876740365432430041619)
  ·
    refine ⟨140059315110548148645062429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93372876740365432430041619 140059315110548148645062429)
    ·
      refine ⟨52522243166455555741898411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140059315110548148645062429 52522243166455555741898411)
      ·
        refine ⟨78783364749683333612847617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52522243166455555741898411 78783364749683333612847617)
        ·
          refine ⟨59087523562262500209635713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78783364749683333612847617 59087523562262500209635713)
          ·
            refine ⟨44315642671696875157226785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59087523562262500209635713 44315642671696875157226785)
            ·
              refine ⟨33236732003772656367920089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44315642671696875157226785 33236732003772656367920089)
              ·
                refine ⟨24927549002829492275940067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33236732003772656367920089 24927549002829492275940067)
                ·
                  refine ⟨37391323504244238413910101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24927549002829492275940067 37391323504244238413910101)
                  ·
                    refine ⟨438179572315362168913009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37391323504244238413910101 438179572315362168913009)
                    ·
                      rfl

theorem cell23_2560055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 8].length) (baseStart_2560055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560055 prefixEnd_2560055 := by exact prefixLift 2560055
  have htrace : WordTrace (prefixWord ++ tailWord_2560055) baseStart_2560055 baseEnd_2560055 := by
    simpa [prefixWord, tailWord_2560055, baseEnd_2560055] using wordTrace_append hprefix tailTrace_2560055
  have hstable : (prefixWord ++ tailWord_2560055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560055).length < 2 ^ (prefixWord ++ tailWord_2560055).sum := by decide
  have hdescent : baseEnd_2560055 < baseStart_2560055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560057 : List Nat := [1, 2, 1, 5, 4, 1, 1, 3, 1, 2, 2]
def baseStart_2560057 : Nat := 118140960795 + 2560057 * 2 ^ 59
def prefixEnd_2560057 : Nat := 4983230072969 + 3 ^ 40 * 2560057 * 2
def baseEnd_2560057 : Nat := 1314539743907395498914019

theorem tailTrace_2560057 : CollatzResearch.WordTrace tailWord_2560057 prefixEnd_2560057 1314539743907395498914019 := by
  unfold tailWord_2560057
  simp only [CollatzResearch.WordTrace]
  refine ⟨93372949686358186771614425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62248633124238791181076283 93372949686358186771614425)
  ·
    refine ⟨70029712264768640078710819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93372949686358186771614425 70029712264768640078710819)
    ·
      refine ⟨105044568397152960118066229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70029712264768640078710819 105044568397152960118066229)
      ·
        refine ⟨9847928287233090011068709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105044568397152960118066229 9847928287233090011068709)
        ·
          refine ⟨1846486553856204377075383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9847928287233090011068709 1846486553856204377075383)
          ·
            refine ⟨2769729830784306565613075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1846486553856204377075383 2769729830784306565613075)
            ·
              refine ⟨4154594746176459848419613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2769729830784306565613075 4154594746176459848419613)
              ·
                refine ⟨1557973029816172443157355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4154594746176459848419613 1557973029816172443157355)
                ·
                  refine ⟨2336959544724258664736033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1557973029816172443157355 2336959544724258664736033)
                  ·
                    refine ⟨1752719658543193998552025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2336959544724258664736033 1752719658543193998552025)
                    ·
                      refine ⟨1314539743907395498914019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1752719658543193998552025 1314539743907395498914019)
                      ·
                        rfl

theorem cell23_2560057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_2560057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560057 prefixEnd_2560057 := by exact prefixLift 2560057
  have htrace : WordTrace (prefixWord ++ tailWord_2560057) baseStart_2560057 baseEnd_2560057 := by
    simpa [prefixWord, tailWord_2560057, baseEnd_2560057] using wordTrace_append hprefix tailTrace_2560057
  have hstable : (prefixWord ++ tailWord_2560057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560057).length < 2 ^ (prefixWord ++ tailWord_2560057).sum := by decide
  have hdescent : baseEnd_2560057 < baseStart_2560057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560136 : List Nat := [2, 1, 3, 4, 1, 2, 1, 4, 5]
def baseStart_2560136 : Nat := 118140960795 + 2560136 * 2 ^ 59
def prefixEnd_2560136 : Nat := 4983230072969 + 3 ^ 40 * 2560136 * 2
def baseEnd_2560136 : Nat := 146064478764344521091795

theorem tailTrace_2560136 : CollatzResearch.WordTrace tailWord_2560136 prefixEnd_2560136 146064478764344521091795 := by
  unfold tailWord_2560136
  simp only [CollatzResearch.WordTrace]
  refine ⟨46687915526535991631870131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62250554035381322175826841 46687915526535991631870131)
  ·
    refine ⟨70031873289803987447805197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46687915526535991631870131 70031873289803987447805197)
    ·
      refine ⟨26261952483676495292926949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70031873289803987447805197 26261952483676495292926949)
      ·
        refine ⟨4924116090689342867423803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26261952483676495292926949 4924116090689342867423803)
        ·
          refine ⟨7386174136034014301135705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4924116090689342867423803 7386174136034014301135705)
          ·
            refine ⟨5539630602025510725851779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7386174136034014301135705 5539630602025510725851779)
            ·
              refine ⟨8309445903038266088777669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5539630602025510725851779 8309445903038266088777669)
              ·
                refine ⟨1558021106819674891645813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8309445903038266088777669 1558021106819674891645813)
                ·
                  refine ⟨146064478764344521091795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1558021106819674891645813 146064478764344521091795)
                  ·
                    rfl

theorem cell23_2560136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4, 5].length) (baseStart_2560136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560136 prefixEnd_2560136 := by exact prefixLift 2560136
  have htrace : WordTrace (prefixWord ++ tailWord_2560136) baseStart_2560136 baseEnd_2560136 := by
    simpa [prefixWord, tailWord_2560136, baseEnd_2560136] using wordTrace_append hprefix tailTrace_2560136
  have hstable : (prefixWord ++ tailWord_2560136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560136).length < 2 ^ (prefixWord ++ tailWord_2560136).sum := by decide
  have hdescent : baseEnd_2560136 < baseStart_2560136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560189 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 4, 2, 3]
def baseStart_2560189 : Nat := 118140960795 + 2560189 * 2 ^ 59
def prefixEnd_2560189 : Nat := 4983230072969 + 3 ^ 40 * 2560189 * 2
def baseEnd_2560189 : Nat := 1314607523353788982463411

theorem tailTrace_2560189 : CollatzResearch.WordTrace tailWord_2560189 prefixEnd_2560189 1314607523353788982463411 := by
  unfold tailWord_2560189
  simp only [CollatzResearch.WordTrace]
  refine ⟨93377764121879973315419621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62251842747919982210279747 93377764121879973315419621)
  ·
    refine ⟨17508330772852494996641179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93377764121879973315419621 17508330772852494996641179)
    ·
      refine ⟨26262496159278742494961769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17508330772852494996641179 26262496159278742494961769)
      ·
        refine ⟨19696872119459056871221327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26262496159278742494961769 19696872119459056871221327)
        ·
          refine ⟨29545308179188585306831991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19696872119459056871221327 29545308179188585306831991)
          ·
            refine ⟨44317962268782877960247987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29545308179188585306831991 44317962268782877960247987)
            ·
              refine ⟨66476943403174316940371981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44317962268782877960247987 66476943403174316940371981)
              ·
                refine ⟨24928853776190368852639493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66476943403174316940371981 24928853776190368852639493)
                ·
                  refine ⟨4674160083035694159869905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24928853776190368852639493 4674160083035694159869905)
                  ·
                    refine ⟨3505620062276770619902429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4674160083035694159869905 3505620062276770619902429)
                    ·
                      refine ⟨1314607523353788982463411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3505620062276770619902429 1314607523353788982463411)
                      ·
                        rfl

theorem cell23_2560189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_2560189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560189 prefixEnd_2560189 := by exact prefixLift 2560189
  have htrace : WordTrace (prefixWord ++ tailWord_2560189) baseStart_2560189 baseEnd_2560189 := by
    simpa [prefixWord, tailWord_2560189, baseEnd_2560189] using wordTrace_append hprefix tailTrace_2560189
  have hstable : (prefixWord ++ tailWord_2560189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560189).length < 2 ^ (prefixWord ++ tailWord_2560189).sum := by decide
  have hdescent : baseEnd_2560189 < baseStart_2560189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560196 : List Nat := [2, 3, 3, 1, 2, 1, 1, 3, 3, 4]
def baseStart_2560196 : Nat := 118140960795 + 2560196 * 2 ^ 59
def prefixEnd_2560196 : Nat := 4983230072969 + 3 ^ 40 * 2560196 * 2
def baseEnd_2560196 : Nat := 438203705906123485025293

theorem tailTrace_2560196 : CollatzResearch.WordTrace tailWord_2560196 prefixEnd_2560196 438203705906123485025293 := by
  unfold tailWord_2560196
  simp only [CollatzResearch.WordTrace]
  refine ⟨46689009716427306755462221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62252012955236409007282961 46689009716427306755462221)
  ·
    refine ⟨17508378643660240033298333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46689009716427306755462221 17508378643660240033298333)
    ·
      refine ⟨6565641991372590012486875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17508378643660240033298333 6565641991372590012486875)
      ·
        refine ⟨9848462987058885018730313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6565641991372590012486875 9848462987058885018730313)
        ·
          refine ⟨7386347240294163764047735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9848462987058885018730313 7386347240294163764047735)
          ·
            refine ⟨11079520860441245646071603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7386347240294163764047735 11079520860441245646071603)
            ·
              refine ⟨16619281290661868469107405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11079520860441245646071603 16619281290661868469107405)
              ·
                refine ⟨6232230483998200675915277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16619281290661868469107405 6232230483998200675915277)
                ·
                  refine ⟨2337086431499325253468229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6232230483998200675915277 2337086431499325253468229)
                  ·
                    refine ⟨438203705906123485025293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2337086431499325253468229 438203705906123485025293)
                    ·
                      rfl

theorem cell23_2560196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_2560196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560196 prefixEnd_2560196 := by exact prefixLift 2560196
  have htrace : WordTrace (prefixWord ++ tailWord_2560196) baseStart_2560196 baseEnd_2560196 := by
    simpa [prefixWord, tailWord_2560196, baseEnd_2560196] using wordTrace_append hprefix tailTrace_2560196
  have hstable : (prefixWord ++ tailWord_2560196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560196).length < 2 ^ (prefixWord ++ tailWord_2560196).sum := by decide
  have hdescent : baseEnd_2560196 < baseStart_2560196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560253 : List Nat := [1, 4, 1, 1, 1, 1, 1, 8, 1, 1, 3]
def baseStart_2560253 : Nat := 118140960795 + 2560253 * 2 ^ 59
def prefixEnd_2560253 : Nat := 4983230072969 + 3 ^ 40 * 2560253 * 2
def baseEnd_2560253 : Nat := 1314640386115676732063117

theorem tailTrace_2560253 : CollatzResearch.WordTrace tailWord_2560253 prefixEnd_2560253 1314640386115676732063117 := by
  unfold tailWord_2560253
  simp only [CollatzResearch.WordTrace]
  refine ⟨93380098393648112245749413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62253398929098741497166275 93380098393648112245749413)
  ·
    refine ⟨17508768448809021046078015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93380098393648112245749413 17508768448809021046078015)
    ·
      refine ⟨26263152673213531569117023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17508768448809021046078015 26263152673213531569117023)
      ·
        refine ⟨39394729009820297353675535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26263152673213531569117023 39394729009820297353675535)
        ·
          refine ⟨59092093514730446030513303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39394729009820297353675535 59092093514730446030513303)
          ·
            refine ⟨88638140272095669045769955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59092093514730446030513303 88638140272095669045769955)
            ·
              refine ⟨132957210408143503568654933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88638140272095669045769955 132957210408143503568654933)
              ·
                refine ⟨1558092309470431682445175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 132957210408143503568654933 1558092309470431682445175)
                ·
                  refine ⟨2337138464205647523667763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1558092309470431682445175 2337138464205647523667763)
                  ·
                    refine ⟨3505707696308471285501645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2337138464205647523667763 3505707696308471285501645)
                    ·
                      refine ⟨1314640386115676732063117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3505707696308471285501645 1314640386115676732063117)
                      ·
                        rfl

theorem cell23_2560253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8, 1, 1, 3].length) (baseStart_2560253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560253 prefixEnd_2560253 := by exact prefixLift 2560253
  have htrace : WordTrace (prefixWord ++ tailWord_2560253) baseStart_2560253 baseEnd_2560253 := by
    simpa [prefixWord, tailWord_2560253, baseEnd_2560253] using wordTrace_append hprefix tailTrace_2560253
  have hstable : (prefixWord ++ tailWord_2560253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560253).length < 2 ^ (prefixWord ++ tailWord_2560253).sum := by decide
  have hdescent : baseEnd_2560253 < baseStart_2560253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560259 : List Nat := [1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 4]
def baseStart_2560259 : Nat := 118140960795 + 2560259 * 2 ^ 59
def prefixEnd_2560259 : Nat := 4983230072969 + 3 ^ 40 * 2560259 * 2
def baseEnd_2560259 : Nat := 1314643466999603708588089

theorem tailTrace_2560259 : CollatzResearch.WordTrace tailWord_2560259 prefixEnd_2560259 1314643466999603708588089 := by
  unfold tailWord_2560259
  simp only [CollatzResearch.WordTrace]
  refine ⟨93380317231626375270467831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62253544821084250180311887 93380317231626375270467831)
  ·
    refine ⟨140070475847439562905701747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93380317231626375270467831 140070475847439562905701747)
    ·
      refine ⟨210105713771159344358552621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140070475847439562905701747 210105713771159344358552621)
      ·
        refine ⟨78789642664184754134457233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210105713771159344358552621 78789642664184754134457233)
        ·
          refine ⟨59092231998138565600842925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78789642664184754134457233 59092231998138565600842925)
          ·
            refine ⟨22159586999301962100316097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59092231998138565600842925 22159586999301962100316097)
            ·
              refine ⟨16619690249476471575237073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22159586999301962100316097 16619690249476471575237073)
              ·
                refine ⟨12464767687107353681427805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16619690249476471575237073 12464767687107353681427805)
                ·
                  refine ⟨4674287882665257630535427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12464767687107353681427805 4674287882665257630535427)
                  ·
                    refine ⟨7011431823997886445803141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4674287882665257630535427 7011431823997886445803141)
                    ·
                      refine ⟨1314643466999603708588089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7011431823997886445803141 1314643466999603708588089)
                      ·
                        rfl

theorem cell23_2560259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_2560259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560259 prefixEnd_2560259 := by exact prefixLift 2560259
  have htrace : WordTrace (prefixWord ++ tailWord_2560259) baseStart_2560259 baseEnd_2560259 := by
    simpa [prefixWord, tailWord_2560259, baseEnd_2560259] using wordTrace_append hprefix tailTrace_2560259
  have hstable : (prefixWord ++ tailWord_2560259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560259).length < 2 ^ (prefixWord ++ tailWord_2560259).sum := by decide
  have hdescent : baseEnd_2560259 < baseStart_2560259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560260 : List Nat := [2, 3, 2, 2, 4, 1, 2, 1, 6]
def baseStart_2560260 : Nat := 118140960795 + 2560260 * 2 ^ 59
def prefixEnd_2560260 : Nat := 4983230072969 + 3 ^ 40 * 2560260 * 2
def baseEnd_2560260 : Nat := 146071553386695356075065

theorem tailTrace_2560260 : CollatzResearch.WordTrace tailWord_2560260 prefixEnd_2560260 146071553386695356075065 := by
  unfold tailWord_2560260
  simp only [CollatzResearch.WordTrace]
  refine ⟨46690176852311376220627117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62253569136415168294169489 46690176852311376220627117)
  ·
    refine ⟨17508816319616766082735169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46690176852311376220627117 17508816319616766082735169)
    ·
      refine ⟨13131612239712574562051377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17508816319616766082735169 13131612239712574562051377)
      ·
        refine ⟨9848709179784430921538533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13131612239712574562051377 9848709179784430921538533)
        ·
          refine ⟨1846632971209580797788475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9848709179784430921538533 1846632971209580797788475)
          ·
            refine ⟨2769949456814371196682713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1846632971209580797788475 2769949456814371196682713)
            ·
              refine ⟨2077462092610778397512035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2769949456814371196682713 2077462092610778397512035)
              ·
                refine ⟨3116193138916167596268053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2077462092610778397512035 3116193138916167596268053)
                ·
                  refine ⟨146071553386695356075065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3116193138916167596268053 146071553386695356075065)
                  ·
                    rfl

theorem cell23_2560260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 6].length) (baseStart_2560260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560260 prefixEnd_2560260 := by exact prefixLift 2560260
  have htrace : WordTrace (prefixWord ++ tailWord_2560260) baseStart_2560260 baseEnd_2560260 := by
    simpa [prefixWord, tailWord_2560260, baseEnd_2560260] using wordTrace_append hprefix tailTrace_2560260
  have hstable : (prefixWord ++ tailWord_2560260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560260).length < 2 ^ (prefixWord ++ tailWord_2560260).sum := by decide
  have hdescent : baseEnd_2560260 < baseStart_2560260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560289 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 3, 2, 4]
def baseStart_2560289 : Nat := 118140960795 + 2560289 * 2 ^ 59
def prefixEnd_2560289 : Nat := 4983230072969 + 3 ^ 40 * 2560289 * 2
def baseEnd_2560289 : Nat := 1314658871419238591212951

theorem tailTrace_2560289 : CollatzResearch.WordTrace tailWord_2560289 prefixEnd_2560289 1314658871419238591212951 := by
  unfold tailWord_2560289
  simp only [CollatzResearch.WordTrace]
  refine ⟨93381411421517690394059921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62254274281011793596039947 93381411421517690394059921)
  ·
    refine ⟨70036058566138267795544941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93381411421517690394059921 70036058566138267795544941)
    ·
      refine ⟨26263521962301850423329353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70036058566138267795544941 26263521962301850423329353)
      ·
        refine ⟨19697641471726387817497015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26263521962301850423329353 19697641471726387817497015)
        ·
          refine ⟨29546462207589581726245523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19697641471726387817497015 29546462207589581726245523)
          ·
            refine ⟨44319693311384372589368285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29546462207589581726245523 44319693311384372589368285)
            ·
              refine ⟨16619884991769139721013107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44319693311384372589368285 16619884991769139721013107)
              ·
                refine ⟨24929827487653709581519661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16619884991769139721013107 24929827487653709581519661)
                ·
                  refine ⟨9348685307870141093069873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24929827487653709581519661 9348685307870141093069873)
                  ·
                    refine ⟨7011513980902605819802405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9348685307870141093069873 7011513980902605819802405)
                    ·
                      refine ⟨1314658871419238591212951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7011513980902605819802405 1314658871419238591212951)
                      ·
                        rfl

theorem cell23_2560289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_2560289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560289 prefixEnd_2560289 := by exact prefixLift 2560289
  have htrace : WordTrace (prefixWord ++ tailWord_2560289) baseStart_2560289 baseEnd_2560289 := by
    simpa [prefixWord, tailWord_2560289, baseEnd_2560289] using wordTrace_append hprefix tailTrace_2560289
  have hstable : (prefixWord ++ tailWord_2560289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560289).length < 2 ^ (prefixWord ++ tailWord_2560289).sum := by decide
  have hdescent : baseEnd_2560289 < baseStart_2560289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560360 : List Nat := [2, 1, 4, 2, 2, 1, 3, 2, 2, 1, 3]
def baseStart_2560360 : Nat := 118140960795 + 2560360 * 2 ^ 59
def prefixEnd_2560360 : Nat := 4983230072969 + 3 ^ 40 * 2560360 * 2
def baseEnd_2560360 : Nat := 1314695328545707813425125

theorem tailTrace_2560360 : CollatzResearch.WordTrace tailWord_2560360 prefixEnd_2560360 1314695328545707813425125 := by
  unfold tailWord_2560360
  simp only [CollatzResearch.WordTrace]
  refine ⟨46692000502130234759947267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62256000669506979679929689 46692000502130234759947267)
  ·
    refine ⟨70038000753195352139920901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46692000502130234759947267 70038000753195352139920901)
    ·
      refine ⟨13132125141224128526235169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70038000753195352139920901 13132125141224128526235169)
      ·
        refine ⟨9849093855918096394676377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13132125141224128526235169 9849093855918096394676377)
        ·
          refine ⟨7386820391938572296007283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9849093855918096394676377 7386820391938572296007283)
          ·
            refine ⟨11080230587907858444010925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7386820391938572296007283 11080230587907858444010925)
            ·
              refine ⟨4155086470465446916504097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11080230587907858444010925 4155086470465446916504097)
              ·
                refine ⟨3116314852849085187378073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4155086470465446916504097 3116314852849085187378073)
                ·
                  refine ⟨2337236139636813890533555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3116314852849085187378073 2337236139636813890533555)
                  ·
                    refine ⟨3505854209455220835800333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2337236139636813890533555 3505854209455220835800333)
                    ·
                      refine ⟨1314695328545707813425125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3505854209455220835800333 1314695328545707813425125)
                      ·
                        rfl

theorem cell23_2560360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_2560360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560360 prefixEnd_2560360 := by exact prefixLift 2560360
  have htrace : WordTrace (prefixWord ++ tailWord_2560360) baseStart_2560360 baseEnd_2560360 := by
    simpa [prefixWord, tailWord_2560360, baseEnd_2560360] using wordTrace_append hprefix tailTrace_2560360
  have hstable : (prefixWord ++ tailWord_2560360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560360).length < 2 ^ (prefixWord ++ tailWord_2560360).sum := by decide
  have hdescent : baseEnd_2560360 < baseStart_2560360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560369 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 4, 1, 5]
def baseStart_2560369 : Nat := 118140960795 + 2560369 * 2 ^ 59
def prefixEnd_2560369 : Nat := 4983230072969 + 3 ^ 40 * 2560369 * 2
def baseEnd_2560369 : Nat := 1314699949871598278212583

theorem tailTrace_2560369 : CollatzResearch.WordTrace tailWord_2560369 prefixEnd_2560369 1314699949871598278212583 := by
  unfold tailWord_2560369
  simp only [CollatzResearch.WordTrace]
  refine ⟨93384329261227864056972161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62256219507485242704648107 93384329261227864056972161)
  ·
    refine ⟨70038246945920898042729121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93384329261227864056972161 70038246945920898042729121)
    ·
      refine ⟨52528685209440673532046841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70038246945920898042729121 52528685209440673532046841)
      ·
        refine ⟨39396513907080505149035131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52528685209440673532046841 39396513907080505149035131)
        ·
          refine ⟨59094770860620757723552697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39396513907080505149035131 59094770860620757723552697)
          ·
            refine ⟨44321078145465568292664523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59094770860620757723552697 44321078145465568292664523)
            ·
              refine ⟨66481617218198352438996785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44321078145465568292664523 66481617218198352438996785)
              ·
                refine ⟨49861212913648764329247589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66481617218198352438996785 49861212913648764329247589)
                ·
                  refine ⟨9348977421309143311733923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49861212913648764329247589 9348977421309143311733923)
                  ·
                    refine ⟨14023466131963714967600885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9348977421309143311733923 14023466131963714967600885)
                    ·
                      refine ⟨1314699949871598278212583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14023466131963714967600885 1314699949871598278212583)
                      ·
                        rfl

theorem cell23_2560369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_2560369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560369 prefixEnd_2560369 := by exact prefixLift 2560369
  have htrace : WordTrace (prefixWord ++ tailWord_2560369) baseStart_2560369 baseEnd_2560369 := by
    simpa [prefixWord, tailWord_2560369, baseEnd_2560369] using wordTrace_append hprefix tailTrace_2560369
  have hstable : (prefixWord ++ tailWord_2560369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560369).length < 2 ^ (prefixWord ++ tailWord_2560369).sum := by decide
  have hdescent : baseEnd_2560369 < baseStart_2560369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560423 : List Nat := [1, 1, 6, 1, 1, 4, 1, 1, 7]
def baseStart_2560423 : Nat := 118140960795 + 2560423 * 2 ^ 59
def prefixEnd_2560423 : Nat := 4983230072969 + 3 ^ 40 * 2560423 * 2
def baseEnd_2560423 : Nat := 146080853091882340770815

theorem tailTrace_2560423 : CollatzResearch.WordTrace tailWord_2560423 prefixEnd_2560423 146080853091882340770815 := by
  unfold tailWord_2560423
  simp only [CollatzResearch.WordTrace]
  refine ⟨93386298803032231279437923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62257532535354820852958615 93386298803032231279437923)
  ·
    refine ⟨140079448204548346919156885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93386298803032231279437923 140079448204548346919156885)
    ·
      refine ⟨6566224134588203761835479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 140079448204548346919156885 6566224134588203761835479)
      ·
        refine ⟨9849336201882305642753219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6566224134588203761835479 9849336201882305642753219)
        ·
          refine ⟨14774004302823458464129829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9849336201882305642753219 14774004302823458464129829)
          ·
            refine ⟨2770125806779398462024343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14774004302823458464129829 2770125806779398462024343)
            ·
              refine ⟨4155188710169097693036515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2770125806779398462024343 4155188710169097693036515)
              ·
                refine ⟨6232783065253646539554773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4155188710169097693036515 6232783065253646539554773)
                ·
                  refine ⟨146080853091882340770815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6232783065253646539554773 146080853091882340770815)
                  ·
                    rfl

theorem cell23_2560423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 7].length) (baseStart_2560423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560423 prefixEnd_2560423 := by exact prefixLift 2560423
  have htrace : WordTrace (prefixWord ++ tailWord_2560423) baseStart_2560423 baseEnd_2560423 := by
    simpa [prefixWord, tailWord_2560423, baseEnd_2560423] using wordTrace_append hprefix tailTrace_2560423
  have hstable : (prefixWord ++ tailWord_2560423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560423).length < 2 ^ (prefixWord ++ tailWord_2560423).sum := by decide
  have hdescent : baseEnd_2560423 < baseStart_2560423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560473 : List Nat := [1, 2, 1, 2, 4, 1, 2, 2, 2, 4, 2]
def baseStart_2560473 : Nat := 118140960795 + 2560473 * 2 ^ 59
def prefixEnd_2560473 : Nat := 4983230072969 + 3 ^ 40 * 2560473 * 2
def baseEnd_2560473 : Nat := 1314753351859665871312105

theorem tailTrace_2560473 : CollatzResearch.WordTrace tailWord_2560473 prefixEnd_2560473 1314753351859665871312105 := by
  unfold tailWord_2560473
  simp only [CollatzResearch.WordTrace]
  refine ⟨93388122452851089818758073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62258748301900726545838715 93388122452851089818758073)
  ·
    refine ⟨70041091839638317364068555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93388122452851089818758073 70041091839638317364068555)
    ·
      refine ⟨105061637759457476046102833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70041091839638317364068555 105061637759457476046102833)
      ·
        refine ⟨78796228319593107034577125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105061637759457476046102833 78796228319593107034577125)
        ·
          refine ⟨14774292809923707568983211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78796228319593107034577125 14774292809923707568983211)
          ·
            refine ⟨22161439214885561353474817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14774292809923707568983211 22161439214885561353474817)
            ·
              refine ⟨16621079411164171015106113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22161439214885561353474817 16621079411164171015106113)
              ·
                refine ⟨12465809558373128261329585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16621079411164171015106113 12465809558373128261329585)
                ·
                  refine ⟨9349357168779846195997189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12465809558373128261329585 9349357168779846195997189)
                  ·
                    refine ⟨1753004469146221161749473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9349357168779846195997189 1753004469146221161749473)
                    ·
                      refine ⟨1314753351859665871312105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1753004469146221161749473 1314753351859665871312105)
                      ·
                        rfl

theorem cell23_2560473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 4, 2].length) (baseStart_2560473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560473 prefixEnd_2560473 := by exact prefixLift 2560473
  have htrace : WordTrace (prefixWord ++ tailWord_2560473) baseStart_2560473 baseEnd_2560473 := by
    simpa [prefixWord, tailWord_2560473, baseEnd_2560473] using wordTrace_append hprefix tailTrace_2560473
  have hstable : (prefixWord ++ tailWord_2560473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560473).length < 2 ^ (prefixWord ++ tailWord_2560473).sum := by decide
  have hdescent : baseEnd_2560473 < baseStart_2560473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560490 : List Nat := [3, 1, 3, 1, 3, 2, 1, 1, 2, 4, 2]
def baseStart_2560490 : Nat := 118140960795 + 2560490 * 2 ^ 59
def prefixEnd_2560490 : Nat := 4983230072969 + 3 ^ 40 * 2560490 * 2
def baseEnd_2560490 : Nat := 1314762081030792304799527

theorem tailTrace_2560490 : CollatzResearch.WordTrace tailWord_2560490 prefixEnd_2560490 1314762081030792304799527 := by
  unfold tailWord_2560490
  simp only [CollatzResearch.WordTrace]
  refine ⟨23347185623447375430531731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62259161662526334481417949 23347185623447375430531731)
  ·
    refine ⟨35020778435171063145797597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23347185623447375430531731 35020778435171063145797597)
    ·
      refine ⟨13132791913189148679674099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35020778435171063145797597 13132791913189148679674099)
      ·
        refine ⟨19699187869783723019511149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13132791913189148679674099 19699187869783723019511149)
        ·
          refine ⟨7387195451168896132316681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19699187869783723019511149 7387195451168896132316681)
          ·
            refine ⟨5540396588376672099237511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7387195451168896132316681 5540396588376672099237511)
            ·
              refine ⟨8310594882565008148856267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5540396588376672099237511 8310594882565008148856267)
              ·
                refine ⟨12465892323847512223284401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8310594882565008148856267 12465892323847512223284401)
                ·
                  refine ⟨9349419242885634167463301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12465892323847512223284401 9349419242885634167463301)
                  ·
                    refine ⟨1753016108041056406399369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9349419242885634167463301 1753016108041056406399369)
                    ·
                      refine ⟨1314762081030792304799527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1753016108041056406399369 1314762081030792304799527)
                      ·
                        rfl

theorem cell23_2560490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_2560490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560490 prefixEnd_2560490 := by exact prefixLift 2560490
  have htrace : WordTrace (prefixWord ++ tailWord_2560490) baseStart_2560490 baseEnd_2560490 := by
    simpa [prefixWord, tailWord_2560490, baseEnd_2560490] using wordTrace_append hprefix tailTrace_2560490
  have hstable : (prefixWord ++ tailWord_2560490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560490).length < 2 ^ (prefixWord ++ tailWord_2560490).sum := by decide
  have hdescent : baseEnd_2560490 < baseStart_2560490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560496 : List Nat := [2, 1, 1, 1, 3, 3, 1, 5, 6]
def baseStart_2560496 : Nat := 118140960795 + 2560496 * 2 ^ 59
def prefixEnd_2560496 : Nat := 4983230072969 + 3 ^ 40 * 2560496 * 2
def baseEnd_2560496 : Nat := 146085017990524364591611

theorem tailTrace_2560496 : CollatzResearch.WordTrace tailWord_2560496 prefixEnd_2560496 146085017990524364591611 := by
  unfold tailWord_2560496
  simp only [CollatzResearch.WordTrace]
  refine ⟨46694480665883882373422671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62259307554511843164563561 46694480665883882373422671)
  ·
    refine ⟨70041720998825823560134007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46694480665883882373422671 70041720998825823560134007)
    ·
      refine ⟨105062581498238735340201011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70041720998825823560134007 105062581498238735340201011)
      ·
        refine ⟨157593872247358103010301517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105062581498238735340201011 157593872247358103010301517)
        ·
          refine ⟨59097702092759288628863069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157593872247358103010301517 59097702092759288628863069)
          ·
            refine ⟨22161638284784733235823651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59097702092759288628863069 22161638284784733235823651)
            ·
              refine ⟨33242457427177099853735477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22161638284784733235823651 33242457427177099853735477)
              ·
                refine ⟨3116480383797853111287701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33242457427177099853735477 3116480383797853111287701)
                ·
                  refine ⟨146085017990524364591611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3116480383797853111287701 146085017990524364591611)
                  ·
                    rfl

theorem cell23_2560496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 6].length) (baseStart_2560496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560496 prefixEnd_2560496 := by exact prefixLift 2560496
  have htrace : WordTrace (prefixWord ++ tailWord_2560496) baseStart_2560496 baseEnd_2560496 := by
    simpa [prefixWord, tailWord_2560496, baseEnd_2560496] using wordTrace_append hprefix tailTrace_2560496
  have hstable : (prefixWord ++ tailWord_2560496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560496).length < 2 ^ (prefixWord ++ tailWord_2560496).sum := by decide
  have hdescent : baseEnd_2560496 < baseStart_2560496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560506 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3]
def baseStart_2560506 : Nat := 118140960795 + 2560506 * 2 ^ 59
def prefixEnd_2560506 : Nat := 4983230072969 + 3 ^ 40 * 2560506 * 2
def baseEnd_2560506 : Nat := 1314770296721264242199453

theorem tailTrace_2560506 : CollatzResearch.WordTrace tailWord_2560506 prefixEnd_2560506 1314770296721264242199453 := by
  unfold tailWord_2560506
  simp only [CollatzResearch.WordTrace]
  refine ⟨23347331515432884113677343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62259550707821024303139581 23347331515432884113677343)
  ·
    refine ⟨35020997273149326170516015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23347331515432884113677343 35020997273149326170516015)
    ·
      refine ⟨52531495909723989255774023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35020997273149326170516015 52531495909723989255774023)
      ·
        refine ⟨78797243864585983883661035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52531495909723989255774023 78797243864585983883661035)
        ·
          refine ⟨118195865796878975825491553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78797243864585983883661035 118195865796878975825491553)
          ·
            refine ⟨88646899347659231869118665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118195865796878975825491553 88646899347659231869118665)
            ·
              refine ⟨66485174510744423901838999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88646899347659231869118665 66485174510744423901838999)
              ·
                refine ⟨99727761766116635852758499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66485174510744423901838999 99727761766116635852758499)
                ·
                  refine ⟨149591642649174953779137749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99727761766116635852758499 149591642649174953779137749)
                  ·
                    refine ⟨3506054124590037979198541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 149591642649174953779137749 3506054124590037979198541)
                    ·
                      refine ⟨1314770296721264242199453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3506054124590037979198541 1314770296721264242199453)
                      ·
                        rfl

theorem cell23_2560506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3].length) (baseStart_2560506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560506 prefixEnd_2560506 := by exact prefixLift 2560506
  have htrace : WordTrace (prefixWord ++ tailWord_2560506) baseStart_2560506 baseEnd_2560506 := by
    simpa [prefixWord, tailWord_2560506, baseEnd_2560506] using wordTrace_append hprefix tailTrace_2560506
  have hstable : (prefixWord ++ tailWord_2560506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560506).length < 2 ^ (prefixWord ++ tailWord_2560506).sum := by decide
  have hdescent : baseEnd_2560506 < baseStart_2560506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560540 : List Nat := [2, 2, 3, 1, 2, 2, 1, 3, 3, 1, 3]
def baseStart_2560540 : Nat := 118140960795 + 2560540 * 2 ^ 59
def prefixEnd_2560540 : Nat := 4983230072969 + 3 ^ 40 * 2560540 * 2
def baseEnd_2560540 : Nat := 1314787755063517109174297

theorem tailTrace_2560540 : CollatzResearch.WordTrace tailWord_2560540 prefixEnd_2560540 1314787755063517109174297 := by
  unfold tailWord_2560540
  simp only [CollatzResearch.WordTrace]
  refine ⟨46695283071804180130723537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62260377429072240174298049 46695283071804180130723537)
  ·
    refine ⟨35021462303853135098042653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46695283071804180130723537 35021462303853135098042653)
    ·
      refine ⟨13133048363944925661765995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35021462303853135098042653 13133048363944925661765995)
      ·
        refine ⟨19699572545917388492648993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13133048363944925661765995 19699572545917388492648993)
        ·
          refine ⟨14774679409438041369486745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19699572545917388492648993 14774679409438041369486745)
          ·
            refine ⟨11081009557078531027115059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14774679409438041369486745 11081009557078531027115059)
            ·
              refine ⟨16621514335617796540672589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11081009557078531027115059 16621514335617796540672589)
              ·
                refine ⟨6233067875856673702752221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16621514335617796540672589 6233067875856673702752221)
                ·
                  refine ⟨2337400453446252638532083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6233067875856673702752221 2337400453446252638532083)
                  ·
                    refine ⟨3506100680169378957798125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2337400453446252638532083 3506100680169378957798125)
                    ·
                      refine ⟨1314787755063517109174297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3506100680169378957798125 1314787755063517109174297)
                      ·
                        rfl

theorem cell23_2560540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_2560540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560540 prefixEnd_2560540 := by exact prefixLift 2560540
  have htrace : WordTrace (prefixWord ++ tailWord_2560540) baseStart_2560540 baseEnd_2560540 := by
    simpa [prefixWord, tailWord_2560540, baseEnd_2560540] using wordTrace_append hprefix tailTrace_2560540
  have hstable : (prefixWord ++ tailWord_2560540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560540).length < 2 ^ (prefixWord ++ tailWord_2560540).sum := by decide
  have hdescent : baseEnd_2560540 < baseStart_2560540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560563 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 2, 6, 2]
def baseStart_2560563 : Nat := 118140960795 + 2560563 * 2 ^ 59
def prefixEnd_2560563 : Nat := 4983230072969 + 3 ^ 40 * 2560563 * 2
def baseEnd_2560563 : Nat := 1314799565118570519186691

theorem tailTrace_2560563 : CollatzResearch.WordTrace tailWord_2560563 prefixEnd_2560563 1314799565118570519186691 := by
  unfold tailWord_2560563
  simp only [CollatzResearch.WordTrace]
  refine ⟨93391405022525035189534343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62260936681683356793022895 93391405022525035189534343)
  ·
    refine ⟨140087107533787552784301515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93391405022525035189534343 140087107533787552784301515)
    ·
      refine ⟨210130661300681329176452273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140087107533787552784301515 210130661300681329176452273)
      ·
        refine ⟨157597995975510996882339205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210130661300681329176452273 157597995975510996882339205)
        ·
          refine ⟨29549624245408311915438601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157597995975510996882339205 29549624245408311915438601)
          ·
            refine ⟨22162218184056233936578951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29549624245408311915438601 22162218184056233936578951)
            ·
              refine ⟨33243327276084350904868427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22162218184056233936578951 33243327276084350904868427)
              ·
                refine ⟨49864990914126526357302641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33243327276084350904868427 49864990914126526357302641)
                ·
                  refine ⟨37398743185594894767976981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49864990914126526357302641 37398743185594894767976981)
                  ·
                    refine ⟨1753066086824760692248921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37398743185594894767976981 1753066086824760692248921)
                    ·
                      refine ⟨1314799565118570519186691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1753066086824760692248921 1314799565118570519186691)
                      ·
                        rfl

theorem cell23_2560563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 6, 2].length) (baseStart_2560563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560563 prefixEnd_2560563 := by exact prefixLift 2560563
  have htrace : WordTrace (prefixWord ++ tailWord_2560563) baseStart_2560563 baseEnd_2560563 := by
    simpa [prefixWord, tailWord_2560563, baseEnd_2560563] using wordTrace_append hprefix tailTrace_2560563
  have hstable : (prefixWord ++ tailWord_2560563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560563).length < 2 ^ (prefixWord ++ tailWord_2560563).sum := by decide
  have hdescent : baseEnd_2560563 < baseStart_2560563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560583 : List Nat := [1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 5]
def baseStart_2560583 : Nat := 118140960795 + 2560583 * 2 ^ 59
def prefixEnd_2560583 : Nat := 4983230072969 + 3 ^ 40 * 2560583 * 2
def baseEnd_2560583 : Nat := 1314809834731660440936599

theorem tailTrace_2560583 : CollatzResearch.WordTrace tailWord_2560583 prefixEnd_2560583 1314809834731660440936599 := by
  unfold tailWord_2560583
  simp only [CollatzResearch.WordTrace]
  refine ⟨93392134482452578605262403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62261422988301719070174935 93392134482452578605262403)
  ·
    refine ⟨140088201723678867907893605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93392134482452578605262403 140088201723678867907893605)
    ·
      refine ⟨26266537823189787732730051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140088201723678867907893605 26266537823189787732730051)
      ·
        refine ⟨39399806734784681599095077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26266537823189787732730051 39399806734784681599095077)
        ·
          refine ⟨7387463762772127799830327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39399806734784681599095077 7387463762772127799830327)
          ·
            refine ⟨11081195644158191699745491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7387463762772127799830327 11081195644158191699745491)
            ·
              refine ⟨16621793466237287549618237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11081195644158191699745491 16621793466237287549618237)
              ·
                refine ⟨6233172549838982831106839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16621793466237287549618237 6233172549838982831106839)
                ·
                  refine ⟨9349758824758474246660259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6233172549838982831106839 9349758824758474246660259)
                  ·
                    refine ⟨14024638237137711369990389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9349758824758474246660259 14024638237137711369990389)
                    ·
                      refine ⟨1314809834731660440936599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14024638237137711369990389 1314809834731660440936599)
                      ·
                        rfl

theorem cell23_2560583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_2560583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560583 prefixEnd_2560583 := by exact prefixLift 2560583
  have htrace : WordTrace (prefixWord ++ tailWord_2560583) baseStart_2560583 baseEnd_2560583 := by
    simpa [prefixWord, tailWord_2560583, baseEnd_2560583] using wordTrace_append hprefix tailTrace_2560583
  have hstable : (prefixWord ++ tailWord_2560583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560583).length < 2 ^ (prefixWord ++ tailWord_2560583).sum := by decide
  have hdescent : baseEnd_2560583 < baseStart_2560583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560586 : List Nat := [3, 1, 2, 1, 1, 4, 11]
def baseStart_2560586 : Nat := 118140960795 + 2560586 * 2 ^ 59
def prefixEnd_2560586 : Nat := 4983230072969 + 3 ^ 40 * 2560586 * 2
def baseEnd_2560586 : Nat := 16232239199674369496285

theorem tailTrace_2560586 : CollatzResearch.WordTrace tailWord_2560586 prefixEnd_2560586 16232239199674369496285 := by
  unfold tailWord_2560586
  simp only [CollatzResearch.WordTrace]
  refine ⟨23348060975360427529405403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62261495934294473411747741 23348060975360427529405403)
  ·
    refine ⟨35022091463040641294108105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23348060975360427529405403 35022091463040641294108105)
    ·
      refine ⟨26266568597280480970581079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35022091463040641294108105 26266568597280480970581079)
      ·
        refine ⟨39399852895920721455871619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26266568597280480970581079 39399852895920721455871619)
        ·
          refine ⟨59099779343881082183807429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39399852895920721455871619 59099779343881082183807429)
          ·
            refine ⟨11081208626977702909463893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59099779343881082183807429 11081208626977702909463893)
            ·
              refine ⟨16232239199674369496285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11081208626977702909463893 16232239199674369496285)
              ·
                rfl

theorem cell23_2560586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 11].length) (baseStart_2560586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560586 prefixEnd_2560586 := by exact prefixLift 2560586
  have htrace : WordTrace (prefixWord ++ tailWord_2560586) baseStart_2560586 baseEnd_2560586 := by
    simpa [prefixWord, tailWord_2560586, baseEnd_2560586] using wordTrace_append hprefix tailTrace_2560586
  have hstable : (prefixWord ++ tailWord_2560586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560586).length < 2 ^ (prefixWord ++ tailWord_2560586).sum := by decide
  have hdescent : baseEnd_2560586 < baseStart_2560586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560597 : List Nat := [1, 3, 2, 2, 1, 1, 5, 1, 3, 2, 2]
def baseStart_2560597 : Nat := 118140960795 + 2560597 * 2 ^ 59
def prefixEnd_2560597 : Nat := 4983230072969 + 3 ^ 40 * 2560597 * 2
def baseEnd_2560597 : Nat := 1314817023460823386161535

theorem tailTrace_2560597 : CollatzResearch.WordTrace tailWord_2560597 prefixEnd_2560597 1314817023460823386161535 := by
  unfold tailWord_2560597
  simp only [CollatzResearch.WordTrace]
  refine ⟨93392645104401858996272045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62261763402934572664181363 93392645104401858996272045)
  ·
    refine ⟨35022241914150697123602017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93392645104401858996272045 35022241914150697123602017)
    ·
      refine ⟨26266681435613022842701513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35022241914150697123602017 26266681435613022842701513)
      ·
        refine ⟨19700011076709767132026135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26266681435613022842701513 19700011076709767132026135)
        ·
          refine ⟨29550016615064650698039203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19700011076709767132026135 29550016615064650698039203)
          ·
            refine ⟨44325024922596976047058805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29550016615064650698039203 44325024922596976047058805)
            ·
              refine ⟨4155471086493466504411763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44325024922596976047058805 4155471086493466504411763)
              ·
                refine ⟨6233206629740199756617645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4155471086493466504411763 6233206629740199756617645)
                ·
                  refine ⟨2337452486152574908731617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6233206629740199756617645 2337452486152574908731617)
                  ·
                    refine ⟨1753089364614431181548713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2337452486152574908731617 1753089364614431181548713)
                    ·
                      refine ⟨1314817023460823386161535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1753089364614431181548713 1314817023460823386161535)
                      ·
                        rfl

theorem cell23_2560597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_2560597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560597 prefixEnd_2560597 := by exact prefixLift 2560597
  have htrace : WordTrace (prefixWord ++ tailWord_2560597) baseStart_2560597 baseEnd_2560597 := by
    simpa [prefixWord, tailWord_2560597, baseEnd_2560597] using wordTrace_append hprefix tailTrace_2560597
  have hstable : (prefixWord ++ tailWord_2560597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560597).length < 2 ^ (prefixWord ++ tailWord_2560597).sum := by decide
  have hdescent : baseEnd_2560597 < baseStart_2560597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560642 : List Nat := [3, 4, 3, 1, 1, 2, 2, 2, 1, 1, 3]
def baseStart_2560642 : Nat := 118140960795 + 2560642 * 2 ^ 59
def prefixEnd_2560642 : Nat := 4983230072969 + 3 ^ 40 * 2560642 * 2
def baseEnd_2560642 : Nat := 1314840130090275710098829

theorem tailTrace_2560642 : CollatzResearch.WordTrace tailWord_2560642 prefixEnd_2560642 1314840130090275710098829 := by
  unfold tailWord_2560642
  simp only [CollatzResearch.WordTrace]
  refine ⟨23348571597309707920415045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62262857592825887787773453 23348571597309707920415045)
  ·
    refine ⟨4377857174495570235077821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23348571597309707920415045 4377857174495570235077821)
    ·
      refine ⟨1641696440435838838154183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4377857174495570235077821 1641696440435838838154183)
      ·
        refine ⟨2462544660653758257231275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1641696440435838838154183 2462544660653758257231275)
        ·
          refine ⟨3693816990980637385846913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2462544660653758257231275 3693816990980637385846913)
          ·
            refine ⟨2770362743235478039385185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3693816990980637385846913 2770362743235478039385185)
            ·
              refine ⟨2077772057426608529538889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2770362743235478039385185 2077772057426608529538889)
              ·
                refine ⟨1558329043069956397154167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2077772057426608529538889 1558329043069956397154167)
                ·
                  refine ⟨2337493564604934595731251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1558329043069956397154167 2337493564604934595731251)
                  ·
                    refine ⟨3506240346907401893596877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2337493564604934595731251 3506240346907401893596877)
                    ·
                      refine ⟨1314840130090275710098829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3506240346907401893596877 1314840130090275710098829)
                      ·
                        rfl

theorem cell23_2560642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_2560642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560642 prefixEnd_2560642 := by exact prefixLift 2560642
  have htrace : WordTrace (prefixWord ++ tailWord_2560642) baseStart_2560642 baseEnd_2560642 := by
    simpa [prefixWord, tailWord_2560642, baseEnd_2560642] using wordTrace_append hprefix tailTrace_2560642
  have hstable : (prefixWord ++ tailWord_2560642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560642).length < 2 ^ (prefixWord ++ tailWord_2560642).sum := by decide
  have hdescent : baseEnd_2560642 < baseStart_2560642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560647 : List Nat := [1, 1, 4, 2, 1, 2, 4, 2, 2, 1, 3]
def baseStart_2560647 : Nat := 118140960795 + 2560647 * 2 ^ 59
def prefixEnd_2560647 : Nat := 4983230072969 + 3 ^ 40 * 2560647 * 2
def baseEnd_2560647 : Nat := 1314842697493548190536305

theorem tailTrace_2560647 : CollatzResearch.WordTrace tailWord_2560647 prefixEnd_2560647 1314842697493548190536305 := by
  unfold tailWord_2560647
  simp only [CollatzResearch.WordTrace]
  refine ⟨93394468754220717535592195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62262979169480478357061463 93394468754220717535592195)
  ·
    refine ⟨140091703131331076303388293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93394468754220717535592195 140091703131331076303388293)
    ·
      refine ⟨26267194337124576806885305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140091703131331076303388293 26267194337124576806885305)
      ·
        refine ⟨19700395752843432605163979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26267194337124576806885305 19700395752843432605163979)
        ·
          refine ⟨29550593629265148907745969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19700395752843432605163979 29550593629265148907745969)
          ·
            refine ⟨22162945221948861680809477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29550593629265148907745969 22162945221948861680809477)
            ·
              refine ⟨4155552229115411565151777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22162945221948861680809477 4155552229115411565151777)
              ·
                refine ⟨3116664171836558673863833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4155552229115411565151777 3116664171836558673863833)
                ·
                  refine ⟨2337498128877419005397875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3116664171836558673863833 2337498128877419005397875)
                  ·
                    refine ⟨3506247193316128508096813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2337498128877419005397875 3506247193316128508096813)
                    ·
                      refine ⟨1314842697493548190536305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3506247193316128508096813 1314842697493548190536305)
                      ·
                        rfl

theorem cell23_2560647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_2560647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560647 prefixEnd_2560647 := by exact prefixLift 2560647
  have htrace : WordTrace (prefixWord ++ tailWord_2560647) baseStart_2560647 baseEnd_2560647 := by
    simpa [prefixWord, tailWord_2560647, baseEnd_2560647] using wordTrace_append hprefix tailTrace_2560647
  have hstable : (prefixWord ++ tailWord_2560647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560647).length < 2 ^ (prefixWord ++ tailWord_2560647).sum := by decide
  have hdescent : baseEnd_2560647 < baseStart_2560647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560663 : List Nat := [1, 1, 3, 3, 2, 1, 3, 1, 2, 6]
def baseStart_2560663 : Nat := 118140960795 + 2560663 * 2 ^ 59
def prefixEnd_2560663 : Nat := 4983230072969 + 3 ^ 40 * 2560663 * 2
def baseEnd_2560663 : Nat := 438283637728006709312077

theorem tailTrace_2560663 : CollatzResearch.WordTrace tailWord_2560663 prefixEnd_2560663 438283637728006709312077 := by
  unfold tailWord_2560663
  simp only [CollatzResearch.WordTrace]
  refine ⟨93395052322162752268174643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62263368214775168178783095 93395052322162752268174643)
  ·
    refine ⟨140092578483244128402261965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93395052322162752268174643 140092578483244128402261965)
    ·
      refine ⟨52534716931216548150848237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140092578483244128402261965 52534716931216548150848237)
      ·
        refine ⟨19700518849206205556568089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52534716931216548150848237 19700518849206205556568089)
        ·
          refine ⟨14775389136904654167426067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19700518849206205556568089 14775389136904654167426067)
          ·
            refine ⟨22163083705356981251139101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14775389136904654167426067 22163083705356981251139101)
            ·
              refine ⟨8311156389508867969177163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22163083705356981251139101 8311156389508867969177163)
              ·
                refine ⟨12466734584263301953765745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8311156389508867969177163 12466734584263301953765745)
                ·
                  refine ⟨9350050938197476465324309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12466734584263301953765745 9350050938197476465324309)
                  ·
                    refine ⟨438283637728006709312077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9350050938197476465324309 438283637728006709312077)
                    ·
                      rfl

theorem cell23_2560663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 6].length) (baseStart_2560663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560663 prefixEnd_2560663 := by exact prefixLift 2560663
  have htrace : WordTrace (prefixWord ++ tailWord_2560663) baseStart_2560663 baseEnd_2560663 := by
    simpa [prefixWord, tailWord_2560663, baseEnd_2560663] using wordTrace_append hprefix tailTrace_2560663
  have hstable : (prefixWord ++ tailWord_2560663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560663).length < 2 ^ (prefixWord ++ tailWord_2560663).sum := by decide
  have hdescent : baseEnd_2560663 < baseStart_2560663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560670 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_2560670 : Nat := 118140960795 + 2560670 * 2 ^ 59
def prefixEnd_2560670 : Nat := 4983230072969 + 3 ^ 40 * 2560670 * 2
def baseEnd_2560670 : Nat := 1314854507548601600548699

theorem tailTrace_2560670 : CollatzResearch.WordTrace tailWord_2560670 prefixEnd_2560670 1314854507548601600548699 := by
  unfold tailWord_2560670
  simp only [CollatzResearch.WordTrace]
  refine ⟨11674413454142174057959933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62263538422091594975786309 11674413454142174057959933)
  ·
    refine ⟨4377905045303315271734975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11674413454142174057959933 4377905045303315271734975)
    ·
      refine ⟨6566857567954972907602463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4377905045303315271734975 6566857567954972907602463)
      ·
        refine ⟨9850286351932459361403695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6566857567954972907602463 9850286351932459361403695)
        ·
          refine ⟨14775429527898689042105543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9850286351932459361403695 14775429527898689042105543)
          ·
            refine ⟨22163144291848033563158315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14775429527898689042105543 22163144291848033563158315)
            ·
              refine ⟨33244716437772050344737473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22163144291848033563158315 33244716437772050344737473)
              ·
                refine ⟨24933537328329037758553105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33244716437772050344737473 24933537328329037758553105)
                ·
                  refine ⟨18700152996246778318914829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24933537328329037758553105 18700152996246778318914829)
                  ·
                    refine ⟨7012557373592541869593061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18700152996246778318914829 7012557373592541869593061)
                    ·
                      refine ⟨1314854507548601600548699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7012557373592541869593061 1314854507548601600548699)
                      ·
                        rfl

theorem cell23_2560670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_2560670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560670 prefixEnd_2560670 := by exact prefixLift 2560670
  have htrace : WordTrace (prefixWord ++ tailWord_2560670) baseStart_2560670 baseEnd_2560670 := by
    simpa [prefixWord, tailWord_2560670, baseEnd_2560670] using wordTrace_append hprefix tailTrace_2560670
  have hstable : (prefixWord ++ tailWord_2560670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560670).length < 2 ^ (prefixWord ++ tailWord_2560670).sum := by decide
  have hdescent : baseEnd_2560670 < baseStart_2560670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560704 : List Nat := [2, 1, 1, 2, 4, 2, 3, 2, 2, 2, 2]
def baseStart_2560704 : Nat := 118140960795 + 2560704 * 2 ^ 59
def prefixEnd_2560704 : Nat := 4983230072969 + 3 ^ 40 * 2560704 * 2
def baseEnd_2560704 : Nat := 1314871965890854467523543

theorem tailTrace_2560704 : CollatzResearch.WordTrace tailWord_2560704 prefixEnd_2560704 1314871965890854467523543 := by
  unfold tailWord_2560704
  simp only [CollatzResearch.WordTrace]
  refine ⟨46698273857507108135208583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62264365143342810846944777 46698273857507108135208583)
  ·
    refine ⟨70047410786260662202812875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46698273857507108135208583 70047410786260662202812875)
    ·
      refine ⟨105071116179390993304219313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70047410786260662202812875 105071116179390993304219313)
      ·
        refine ⟨78803337134543244978164485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105071116179390993304219313 78803337134543244978164485)
        ·
          refine ⟨14775625712726858433405841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78803337134543244978164485 14775625712726858433405841)
          ·
            refine ⟨11081719284545143825054381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14775625712726858433405841 11081719284545143825054381)
            ·
              refine ⟨4155644731704428934395393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11081719284545143825054381 4155644731704428934395393)
              ·
                refine ⟨3116733548778321700796545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4155644731704428934395393 3116733548778321700796545)
                ·
                  refine ⟨2337550161583741275597409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3116733548778321700796545 2337550161583741275597409)
                  ·
                    refine ⟨1753162621187805956698057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2337550161583741275597409 1753162621187805956698057)
                    ·
                      refine ⟨1314871965890854467523543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1753162621187805956698057 1314871965890854467523543)
                      ·
                        rfl

theorem cell23_2560704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 2, 2, 2].length) (baseStart_2560704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560704 prefixEnd_2560704 := by exact prefixLift 2560704
  have htrace : WordTrace (prefixWord ++ tailWord_2560704) baseStart_2560704 baseEnd_2560704 := by
    simpa [prefixWord, tailWord_2560704, baseEnd_2560704] using wordTrace_append hprefix tailTrace_2560704
  have hstable : (prefixWord ++ tailWord_2560704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560704).length < 2 ^ (prefixWord ++ tailWord_2560704).sum := by decide
  have hdescent : baseEnd_2560704 < baseStart_2560704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2560744 : List Nat := [2, 1, 4, 1, 4, 2, 1, 3, 5]
def baseStart_2560744 : Nat := 118140960795 + 2560744 * 2 ^ 59
def prefixEnd_2560744 : Nat := 4983230072969 + 3 ^ 40 * 2560744 * 2
def baseEnd_2560744 : Nat := 146099167235226034558151

theorem tailTrace_2560744 : CollatzResearch.WordTrace tailWord_2560744 prefixEnd_2560744 146099167235226034558151 := by
  unfold tailWord_2560744
  simp only [CollatzResearch.WordTrace]
  refine ⟨46699003317434651550936643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62265337756579535401248857 46699003317434651550936643)
  ·
    refine ⟨70048504976151977326404965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46699003317434651550936643 70048504976151977326404965)
    ·
      refine ⟨13134094683028495748700931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70048504976151977326404965 13134094683028495748700931)
      ·
        refine ⟨19701142024542743623051397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13134094683028495748700931 19701142024542743623051397)
        ·
          refine ⟨3693964129601764429322137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19701142024542743623051397 3693964129601764429322137)
          ·
            refine ⟨2770473097201323321991603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3693964129601764429322137 2770473097201323321991603)
            ·
              refine ⟨4155709645801984982987405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2770473097201323321991603 4155709645801984982987405)
              ·
                refine ⟨1558391117175744368620277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4155709645801984982987405 1558391117175744368620277)
                ·
                  refine ⟨146099167235226034558151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1558391117175744368620277 146099167235226034558151)
                  ·
                    rfl

theorem cell23_2560744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3, 5].length) (baseStart_2560744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2560744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2560744 prefixEnd_2560744 := by exact prefixLift 2560744
  have htrace : WordTrace (prefixWord ++ tailWord_2560744) baseStart_2560744 baseEnd_2560744 := by
    simpa [prefixWord, tailWord_2560744, baseEnd_2560744] using wordTrace_append hprefix tailTrace_2560744
  have hstable : (prefixWord ++ tailWord_2560744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2560744).length < 2 ^ (prefixWord ++ tailWord_2560744).sum := by decide
  have hdescent : baseEnd_2560744 < baseStart_2560744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2560744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
